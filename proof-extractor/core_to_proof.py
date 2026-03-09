#!/usr/bin/env python3
"""
Convert Z3 unsat core to ordered Dafny proof.

1. Get unsat core from Z3 (named assertions)
2. Parse each assertion's SMT expression
3. Build dependency DAG (A depends on B if A uses terms from B)
4. Topological sort → ordering
5. Map each assertion to Dafny using the mapping chain
6. Create ghost vars for unmapped Z3 variables
"""

import json
import os
import re
import subprocess
import tempfile
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Dict, List, Set, Tuple, Optional


@dataclass
class SMTExpr:
    """Parsed SMT expression."""
    raw: str
    kind: str  # 'atom', 'app', 'let', 'forall', 'exists'
    head: Optional[str] = None  # Function/operator name
    args: List['SMTExpr'] = field(default_factory=list)

    def get_symbols(self) -> Set[str]:
        """Get all symbols (variables/functions) used in this expression."""
        symbols = set()
        if self.kind == 'atom' and self.head:
            symbols.add(self.head)
        elif self.head:
            symbols.add(self.head)
        for arg in self.args:
            symbols.update(arg.get_symbols())
        return symbols


@dataclass
class NamedAssertion:
    """A named assertion from the SMT file."""
    name: str
    expr: SMTExpr
    raw_smt: str
    defines: Set[str] = field(default_factory=set)  # Symbols this assertion defines
    uses: Set[str] = field(default_factory=set)     # Symbols this assertion uses


class SMTParser:
    """Parse SMT-LIB S-expressions."""

    def __init__(self, text: str):
        self.text = text
        self.pos = 0

    def parse(self) -> SMTExpr:
        """Parse an S-expression."""
        self._skip_whitespace()

        if self.pos >= len(self.text):
            return SMTExpr(raw="", kind="atom")

        if self.text[self.pos] == '(':
            return self._parse_list()
        else:
            return self._parse_atom()

    def _skip_whitespace(self):
        while self.pos < len(self.text) and self.text[self.pos] in ' \t\n\r':
            self.pos += 1

    def _parse_atom(self) -> SMTExpr:
        start = self.pos
        while self.pos < len(self.text) and self.text[self.pos] not in '() \t\n\r':
            self.pos += 1
        value = self.text[start:self.pos]
        return SMTExpr(raw=value, kind="atom", head=value)

    def _parse_list(self) -> SMTExpr:
        start = self.pos
        self.pos += 1  # Skip '('
        self._skip_whitespace()

        items = []
        while self.pos < len(self.text) and self.text[self.pos] != ')':
            items.append(self.parse())
            self._skip_whitespace()

        if self.pos < len(self.text):
            self.pos += 1  # Skip ')'

        raw = self.text[start:self.pos]

        if not items:
            return SMTExpr(raw=raw, kind="app")

        head_item = items[0]
        head = head_item.head if head_item.kind == 'atom' else None

        # Determine kind
        if head in ('let', 'forall', 'exists'):
            kind = head
        else:
            kind = 'app'

        return SMTExpr(raw=raw, kind=kind, head=head, args=items[1:])


class MappingChain:
    """
    Complete mapping chain: SMT → Boogie → Dafny
    Uses ONLY the mapping files, no pattern matching.
    """

    def __init__(self, ast_mapping: dict, name_map: dict):
        self.ast_mapping = ast_mapping
        self.name_map = name_map

        # Build reverse mappings
        # SMT name ($generated@@N) → Boogie name
        self.smt_to_boogie: Dict[str, str] = {}
        for smt_name, boogie_name in name_map.get('variables', {}).items():
            self.smt_to_boogie[smt_name] = boogie_name
        for smt_name, boogie_name in name_map.get('assertions', {}).items():
            self.smt_to_boogie[smt_name] = boogie_name

        # Boogie name → Dafny name
        self.boogie_to_dafny: Dict[str, str] = {}
        for method in ast_mapping.get('methods', []):
            for var_name, var_info in method.get('variables', {}).items():
                boogie_name = var_info.get('boogieName', '')
                dafny_name = var_info.get('dafnyName', var_name)
                self.boogie_to_dafny[boogie_name] = dafny_name
                # Also without SSA suffix
                base = boogie_name.split('#')[0]
                self.boogie_to_dafny[base] = dafny_name

        for func in ast_mapping.get('functions', []):
            boogie_name = func.get('boogieName', '')
            dafny_name = func.get('dafnyName', '')
            self.boogie_to_dafny[boogie_name] = dafny_name

        # Track which variables need ghost declarations
        self.ghost_vars: Dict[str, str] = {}  # SMT name → Dafny ghost var name
        self.ghost_counter = 0

    def smt_to_dafny(self, smt_name: str) -> str:
        """Map SMT name to Dafny name, creating ghost var if needed."""
        # First try direct mapping
        boogie = self.smt_to_boogie.get(smt_name)
        if boogie:
            dafny = self.boogie_to_dafny.get(boogie)
            if dafny:
                return dafny
            # Have Boogie but no Dafny → use Boogie name cleaned up
            return self._clean_boogie_name(boogie)

        # No mapping → need ghost variable
        if smt_name not in self.ghost_vars:
            self.ghost_counter += 1
            self.ghost_vars[smt_name] = f"ghost_{self.ghost_counter}"

        return self.ghost_vars[smt_name]

    def _clean_boogie_name(self, name: str) -> str:
        """Clean Boogie name for Dafny use."""
        # Remove module prefix
        if '_module.__default.' in name:
            name = name.split('.')[-1]
        # Remove SSA suffix for readability
        if '#' in name:
            name = name.split('#')[0]
        return name

    def expr_to_dafny(self, expr: SMTExpr) -> str:
        """Convert SMT expression to Dafny syntax using mappings."""
        if expr.kind == 'atom':
            if expr.head is None:
                return ""
            # Check if it's a number
            if expr.head.lstrip('-').isdigit():
                return expr.head
            # Check if it's a boolean
            if expr.head in ('true', 'false'):
                return expr.head
            # Map the symbol
            return self.smt_to_dafny(expr.head)

        elif expr.kind == 'app':
            if not expr.head:
                return ""

            # Map the function/operator
            op = self.smt_to_dafny(expr.head)
            args = [self.expr_to_dafny(a) for a in expr.args]

            # Handle standard SMT operators
            if expr.head == '=':
                return f"({args[0]} == {args[1]})" if len(args) >= 2 else ""
            elif expr.head == 'not':
                return f"!({args[0]})" if args else ""
            elif expr.head == 'and':
                return f"({' && '.join(args)})"
            elif expr.head == 'or':
                return f"({' || '.join(args)})"
            elif expr.head == '=>':
                return f"({args[0]} ==> {args[1]})" if len(args) >= 2 else ""
            elif expr.head in ('+', '-', '*', '/', 'div', 'mod'):
                op_map = {'div': '/', 'mod': '%'}
                op_sym = op_map.get(expr.head, expr.head)
                return f"({args[0]} {op_sym} {args[1]})" if len(args) >= 2 else ""
            elif expr.head in ('<', '>', '<=', '>='):
                return f"({args[0]} {expr.head} {args[1]})" if len(args) >= 2 else ""
            else:
                # Function call
                if args:
                    return f"{op}({', '.join(args)})"
                else:
                    return op

        elif expr.kind in ('forall', 'exists'):
            # Quantifiers - translate structure
            quantifier = 'forall' if expr.kind == 'forall' else 'exists'
            # args[0] is bindings, args[1] is body (possibly with patterns)
            if len(expr.args) >= 2:
                body = self.expr_to_dafny(expr.args[-1])
                return f"{quantifier} ... :: {body}"
            return f"{quantifier} ..."

        elif expr.kind == 'let':
            # Let bindings - inline them
            if len(expr.args) >= 2:
                return self.expr_to_dafny(expr.args[-1])
            return ""

        return expr.raw


class DependencyDAG:
    """Build and analyze dependency DAG from assertions."""

    def __init__(self):
        self.nodes: Dict[str, NamedAssertion] = {}
        self.edges: Dict[str, Set[str]] = defaultdict(set)  # node → nodes it depends on

    def add_assertion(self, assertion: NamedAssertion):
        """Add an assertion to the DAG."""
        self.nodes[assertion.name] = assertion

    def build_edges(self):
        """Build dependency edges based on symbol usage."""
        # Collect what each assertion defines
        defined_by: Dict[str, str] = {}  # symbol → assertion that defines it

        for name, assertion in self.nodes.items():
            for symbol in assertion.defines:
                defined_by[symbol] = name

        # Build edges: A → B if A uses a symbol defined by B
        for name, assertion in self.nodes.items():
            for symbol in assertion.uses:
                if symbol in defined_by and defined_by[symbol] != name:
                    self.edges[name].add(defined_by[symbol])

    def topological_sort(self) -> List[str]:
        """Return assertions in dependency order (dependencies first)."""
        visited = set()
        result = []

        def visit(node: str):
            if node in visited:
                return
            visited.add(node)
            for dep in self.edges.get(node, []):
                if dep in self.nodes:
                    visit(dep)
            result.append(node)

        for node in self.nodes:
            visit(node)

        return result


class CoreToProof:
    """Main pipeline: unsat core → ordered Dafny proof."""

    def __init__(self, smt_file: str, ast_mapping: dict, name_map: dict):
        with open(smt_file) as f:
            self.smt_content = f.read()

        self.mapping = MappingChain(ast_mapping, name_map)
        self.assertions: Dict[str, NamedAssertion] = {}

    def extract_named_assertions(self):
        """Extract all named assertions from SMT file."""
        # Pattern: (assert (! expr :named name))
        pattern = r'\(assert\s+\(!\s+(.*?)\s+:named\s+(\S+)\)\)'

        for match in re.finditer(pattern, self.smt_content, re.DOTALL):
            expr_str = match.group(1)
            name = match.group(2)

            # Parse the expression
            parser = SMTParser(expr_str)
            expr = parser.parse()

            # Extract symbols
            symbols = expr.get_symbols()

            self.assertions[name] = NamedAssertion(
                name=name,
                expr=expr,
                raw_smt=expr_str,
                uses=symbols
            )

    def get_unsat_core(self, timeout: int = 60) -> List[str]:
        """Run Z3 and get ALL unsat cores (one per VC)."""
        # Add unsat core production
        modified = "(set-option :produce-unsat-cores true)\n" + self.smt_content
        modified = modified.replace("(check-sat)", "(check-sat)\n(get-unsat-core)")

        with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as f:
            f.write(modified)
            tmp_file = f.name

        try:
            result = subprocess.run(
                ['z3', f'-T:{timeout}', tmp_file],
                capture_output=True, text=True, timeout=timeout + 10
            )

            output = result.stdout.strip()
            all_cores = []
            is_unsat = False

            for line in output.split('\n'):
                line = line.strip()
                if line == 'unsat':
                    is_unsat = True
                elif is_unsat and line.startswith('(') and not line.startswith('(:'):
                    core_str = line.strip('()')
                    core = [c.strip() for c in core_str.split() if c.strip()]
                    all_cores.extend(core)
                    is_unsat = False  # Reset for next VC
                elif line in ('sat', 'unknown'):
                    is_unsat = False

            # Return unique cores
            return list(dict.fromkeys(all_cores))
        finally:
            os.unlink(tmp_file)

    def build_proof(self, core: List[str]) -> List[str]:
        """Build ordered Dafny proof from unsat core."""
        # Filter to only core assertions
        dag = DependencyDAG()
        for name in core:
            if name in self.assertions:
                dag.add_assertion(self.assertions[name])

        # Build dependency edges
        dag.build_edges()

        # Get topological order
        ordered = dag.topological_sort()

        # Generate Dafny assertions
        proof_lines = []

        # First, declare ghost variables if any
        if self.mapping.ghost_vars:
            proof_lines.append("// Ghost variables for Z3-only terms")
            for smt_name, ghost_name in self.mapping.ghost_vars.items():
                proof_lines.append(f"ghost var {ghost_name}; // from {smt_name}")
            proof_lines.append("")

        # Then, the assertions in order
        for name in ordered:
            if name in self.assertions:
                assertion = self.assertions[name]
                dafny_expr = self.mapping.expr_to_dafny(assertion.expr)
                if dafny_expr:
                    proof_lines.append(f"assert {dafny_expr};  // {name}")

        return proof_lines


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Convert Z3 unsat core to Dafny proof")
    parser.add_argument('smt_file', help='SMT file from Dafny/Boogie')
    parser.add_argument('--ast-mapping', required=True, help='AST mapping JSON from Dafny')
    parser.add_argument('--name-map', required=True, help='Name map JSON from Boogie')
    parser.add_argument('-o', '--output', help='Output file')
    args = parser.parse_args()

    with open(args.ast_mapping) as f:
        ast_mapping = json.load(f)

    with open(args.name_map) as f:
        name_map = json.load(f)

    converter = CoreToProof(args.smt_file, ast_mapping, name_map)
    converter.extract_named_assertions()

    core = converter.get_unsat_core()
    print(f"Unsat core: {len(core)} assertions")

    proof_lines = converter.build_proof(core)

    output = '\n'.join(proof_lines)

    if args.output:
        with open(args.output, 'w') as f:
            f.write(output)
        print(f"Output: {args.output}")
    else:
        print("\n=== Generated Proof ===")
        print(output)


if __name__ == "__main__":
    main()
