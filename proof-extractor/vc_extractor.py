#!/usr/bin/env python3
"""
Extract VCs from Boogie and create SMT queries with proper name mapping.

This module parses Boogie files to extract verification conditions,
creates SMT queries with named assertions, and maps unsat cores back
to Dafny-level assertions.
"""

import re
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple


@dataclass
class BoogieExpr:
    """A parsed Boogie expression."""
    raw: str
    kind: str  # 'var', 'func_call', 'binop', 'literal', 'seq_op'
    children: List['BoogieExpr'] = field(default_factory=list)
    name: Optional[str] = None  # For variables and functions
    operator: Optional[str] = None  # For binary ops


@dataclass
class VCComponent:
    """A component of a verification condition with its SMT encoding."""
    boogie_expr: str
    dafny_expr: str
    smt_name: str  # Name to use in SMT for unsat core


class BoogieExprParser:
    """Parse Boogie expressions into structured form."""

    # Mapping from Boogie to Dafny
    BOOGIE_TO_DAFNY = {
        'Seq#Take': lambda args: f"{args[0]}[..{args[1]}]",
        'Seq#Drop': lambda args: f"{args[0]}[{args[1]}..]",
        'Seq#Length': lambda args: f"|{args[0]}|",
        'Seq#Index': lambda args: f"{args[0]}[{args[1]}]",
        'Seq#Equal': lambda args: f"{args[0]} == {args[1]}",
        'Set#Card': lambda args: f"|{args[0]}|",
        'Set#Subset': lambda args: f"{args[0]} <= {args[1]}",
        'Set#Empty': lambda args: "{}",
        'Set#Difference': lambda args: f"{args[0]} - {args[1]}",
        'Set#UnionOne': lambda args: f"{args[0]} + {{{args[1]}}}",
        'Set#Member': lambda args: f"{args[1]} in {args[0]}",
        'LitInt': lambda args: args[0],
    }

    def __init__(self, var_mapping: Dict[str, str], func_mapping: Dict[str, str]):
        """
        var_mapping: Boogie var name -> Dafny var name (e.g., 'sum#0' -> 'sum')
        func_mapping: Boogie func name -> Dafny func name (e.g., '_module.__default.Sum' -> 'Sum')
        """
        self.var_mapping = var_mapping
        self.func_mapping = func_mapping

    def parse(self, expr: str) -> BoogieExpr:
        """Parse a Boogie expression."""
        expr = expr.strip()

        # Check for binary operators
        for op in ['==', '!=', '<=', '>=', '<', '>', '+', '-', '*', '/', '&&', '||', '==>']:
            # Simple split (doesn't handle nested parens properly, but works for most cases)
            if f' {op} ' in expr and not self._is_inside_parens(expr, expr.find(f' {op} ')):
                parts = expr.split(f' {op} ', 1)
                return BoogieExpr(
                    raw=expr,
                    kind='binop',
                    operator=op,
                    children=[self.parse(parts[0]), self.parse(parts[1])]
                )

        # Check for function calls: FuncName(args) or FuncName#suffix(args)
        func_match = re.match(r'^([\w#@.]+)\((.*)\)$', expr)
        if func_match:
            func_name = func_match.group(1)
            args_str = func_match.group(2)
            args = self._split_args(args_str)
            return BoogieExpr(
                raw=expr,
                kind='func_call',
                name=func_name,
                children=[self.parse(arg) for arg in args]
            )

        # Check for variable (possibly with # suffix)
        if re.match(r'^[\w#@]+$', expr):
            return BoogieExpr(raw=expr, kind='var', name=expr)

        # Literal
        if re.match(r'^-?\d+$', expr):
            return BoogieExpr(raw=expr, kind='literal', name=expr)

        # Unknown - return as-is
        return BoogieExpr(raw=expr, kind='unknown')

    def _is_inside_parens(self, s: str, pos: int) -> bool:
        """Check if position is inside parentheses."""
        depth = 0
        for i, c in enumerate(s):
            if i >= pos:
                return depth > 0
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
        return False

    def _split_args(self, args_str: str) -> List[str]:
        """Split function arguments, respecting nested parens."""
        args = []
        current = []
        depth = 0

        for c in args_str:
            if c == ',' and depth == 0:
                args.append(''.join(current).strip())
                current = []
            else:
                if c == '(':
                    depth += 1
                elif c == ')':
                    depth -= 1
                current.append(c)

        if current:
            args.append(''.join(current).strip())

        return [a for a in args if a]

    def to_dafny(self, expr: BoogieExpr) -> str:
        """Convert a Boogie expression to Dafny syntax."""
        if expr.kind == 'var':
            # Map variable name
            base_name = expr.name.split('#')[0] if '#' in expr.name else expr.name
            return self.var_mapping.get(expr.name, self.var_mapping.get(base_name, expr.name))

        elif expr.kind == 'literal':
            return expr.name

        elif expr.kind == 'binop':
            left = self.to_dafny(expr.children[0])
            right = self.to_dafny(expr.children[1])
            return f"{left} {expr.operator} {right}"

        elif expr.kind == 'func_call':
            args = [self.to_dafny(c) for c in expr.children]

            # Check for built-in Boogie functions
            func_base = expr.name.split('#')[0] if '#' in expr.name else expr.name
            for prefix in ['Seq#', 'Set#', 'Map#', 'LitInt']:
                if expr.name.startswith(prefix) or func_base.startswith(prefix):
                    full_name = expr.name if expr.name.startswith(prefix) else f"{prefix}{func_base.split(prefix)[-1]}"
                    if full_name in self.BOOGIE_TO_DAFNY:
                        return self.BOOGIE_TO_DAFNY[full_name](args)

            # User-defined function
            dafny_func = self.func_mapping.get(expr.name, expr.name)
            # Clean up the function name
            if '.' in dafny_func:
                dafny_func = dafny_func.split('.')[-1]

            # Filter out $LS/$LZ arguments (Dafny internals)
            clean_args = [a for a in args if not a.startswith('$')]

            return f"{dafny_func}({', '.join(clean_args)})"

        return expr.raw

    def extract_subexpressions(self, expr: BoogieExpr) -> List[Tuple[str, str]]:
        """Extract all subexpressions with their Dafny translations."""
        results = []

        def traverse(e: BoogieExpr):
            dafny = self.to_dafny(e)
            if e.kind in ('func_call', 'binop') and len(dafny) > 3:
                results.append((e.raw, dafny))
            for child in e.children:
                traverse(child)

        traverse(expr)
        return results


class VCExtractor:
    """Extract verification conditions from Boogie files."""

    def __init__(self, boogie_content: str, ast_mapping: dict):
        self.content = boogie_content
        self.lines = boogie_content.split('\n')
        self.ast_mapping = ast_mapping

        # Build mappings from AST
        self.var_mapping = {}  # Boogie name -> Dafny name
        self.func_mapping = {}  # Boogie name -> Dafny name

        for method in ast_mapping.get('methods', []):
            for var_name, var_info in method.get('variables', {}).items():
                boogie_name = var_info.get('boogieName', '')
                self.var_mapping[boogie_name] = var_info.get('dafnyName', var_name)
                # Also map without #N suffix
                base = boogie_name.split('#')[0] if '#' in boogie_name else boogie_name
                self.var_mapping[base] = var_info.get('dafnyName', var_name)

        for func in ast_mapping.get('functions', []):
            self.func_mapping[func.get('boogieName', '')] = func.get('dafnyName', '')

    def extract_invariant_expr(self, invariant_id: str) -> Optional[str]:
        """Extract the Boogie expression for an invariant."""
        pattern = rf'invariant\s*\{{:id\s*"{invariant_id}"\}}\s*.*?==>\s*(.+?);'

        for line in self.lines:
            match = re.search(pattern, line)
            if match:
                return match.group(1).strip()

        return None

    def extract_loop_body_effects(self, invariant_id: str) -> List[Tuple[str, str]]:
        """Extract variable assignments from the loop body."""
        effects = []
        in_loop = False

        for i, line in enumerate(self.lines):
            if f'invariant {{:id "{invariant_id}"}}' in line:
                in_loop = True
                continue

            if in_loop:
                # Look for assignments: var := expr;
                assign_match = re.match(r'\s*(\w+#\d+)\s*:=\s*(.+?);', line)
                if assign_match:
                    var = assign_match.group(1)
                    expr = assign_match.group(2)
                    effects.append((var, expr))

                # Stop at loop end or next invariant
                if 'invariant' in line or line.strip() == '}':
                    break

        return effects

    def create_vc_components(self, invariant_id: str, invariant_text: str) -> List[VCComponent]:
        """Create VC components for an invariant with SMT names."""
        components = []

        # Get the Boogie expression
        boogie_expr = self.extract_invariant_expr(invariant_id)
        if not boogie_expr:
            return components

        # Parse it
        parser = BoogieExprParser(self.var_mapping, self.func_mapping)
        parsed = parser.parse(boogie_expr)

        # Extract subexpressions
        subexprs = parser.extract_subexpressions(parsed)

        # Create named components
        for i, (boogie, dafny) in enumerate(subexprs):
            components.append(VCComponent(
                boogie_expr=boogie,
                dafny_expr=dafny,
                smt_name=f"vc_{invariant_id}_{i}"
            ))

        return components


def test():
    """Test the parser."""
    var_map = {'sum#0': 'sum', 's#0': 's', 'i#0': 'i'}
    func_map = {'_module.__default.Sum': 'Sum'}

    parser = BoogieExprParser(var_map, func_map)

    # Test expression
    expr = "sum#0 == _module.__default.Sum($LS($LS($LZ)), Seq#Take(s#0, i#0))"
    parsed = parser.parse(expr)
    dafny = parser.to_dafny(parsed)
    print(f"Boogie: {expr}")
    print(f"Dafny:  {dafny}")

    # Extract subexpressions
    print("\nSubexpressions:")
    for boogie, dafny in parser.extract_subexpressions(parsed):
        print(f"  {boogie} -> {dafny}")


if __name__ == "__main__":
    test()
