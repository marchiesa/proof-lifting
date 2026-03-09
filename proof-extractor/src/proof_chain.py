"""Extract proof chains from Z3's let-based proof format.

Z3 proofs use let-bindings to build a DAG:
  (let ((?x1 expr1))
  (let ((?x2 expr2))   ; can reference ?x1
  (let ((@p1 (rule ...)))  ; proof step
  ...)))

This module resolves the bindings and extracts readable proof chains.
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Any, Tuple
from sexpr_parser import SExpr, Atom, SList, parse_sexpr


@dataclass
class ProofNode:
    """A node in the proof tree."""
    rule: str                          # e.g., "trans", "mp", "quant-inst", "rewrite"
    conclusion: Any                    # What this step proves
    premises: List['ProofNode'] = field(default_factory=list)  # Earlier steps used
    args: List[Any] = field(default_factory=list)              # Rule arguments
    raw: Optional[SExpr] = None

    def __repr__(self):
        return f"ProofNode({self.rule}, {len(self.premises)} premises)"


class ProofChainExtractor:
    """Extract proof chains from Z3 proof output."""

    def __init__(self, name_map: Dict[str, str] = None):
        self.name_map = name_map or {}
        self.bindings: Dict[str, SExpr] = {}  # ?x1 -> expr, @p1 -> proof
        self.proof_cache: Dict[str, ProofNode] = {}

    def extract(self, proof_sexpr: SExpr) -> Optional[ProofNode]:
        """Extract the proof tree from a Z3 proof S-expression."""
        self.bindings = {}
        self.proof_cache = {}

        # Resolve all let-bindings first
        core = self._resolve_lets(proof_sexpr)

        # Now extract the proof tree
        if core:
            return self._extract_proof(core)
        return None

    def _resolve_lets(self, expr: SExpr) -> Optional[SExpr]:
        """Recursively resolve let-bindings and store them."""
        if isinstance(expr, Atom):
            return expr

        if not isinstance(expr, SList) or len(expr.items) == 0:
            return expr

        head = expr.items[0]
        if isinstance(head, Atom) and head.value == 'let':
            # (let ((name value)) body)
            if len(expr.items) >= 3:
                bindings_list = expr.items[1]
                body = expr.items[2]

                if isinstance(bindings_list, SList):
                    for binding in bindings_list.items:
                        if isinstance(binding, SList) and len(binding.items) >= 2:
                            name = binding.items[0]
                            value = binding.items[1]
                            if isinstance(name, Atom):
                                self.bindings[name.value] = value

                return self._resolve_lets(body)

        return expr

    def _extract_proof(self, expr: SExpr) -> Optional[ProofNode]:
        """Extract a proof node from an expression."""
        if isinstance(expr, Atom):
            # Could be a reference to a bound proof term
            if expr.value.startswith('@'):
                if expr.value in self.proof_cache:
                    return self.proof_cache[expr.value]
                if expr.value in self.bindings:
                    node = self._extract_proof(self.bindings[expr.value])
                    if node:
                        self.proof_cache[expr.value] = node
                    return node
            return None

        if not isinstance(expr, SList) or len(expr.items) == 0:
            return None

        head = expr.items[0]
        if not isinstance(head, Atom):
            return None

        rule = head.value

        # Handle different proof rules
        if rule == 'trans':
            # (trans proof1 proof2) - transitivity
            premises = []
            for arg in expr.items[1:]:
                p = self._extract_proof(arg)
                if p:
                    premises.append(p)
            return ProofNode(rule='trans', conclusion=None, premises=premises, raw=expr)

        elif rule == 'trans*':
            # (trans* proof1 proof2 ...) - chained transitivity
            premises = []
            for arg in expr.items[1:]:
                p = self._extract_proof(arg)
                if p:
                    premises.append(p)
            return ProofNode(rule='trans*', conclusion=None, premises=premises, raw=expr)

        elif rule == 'mp':
            # (mp proof1 proof2 conclusion)
            premises = []
            conclusion = None
            for i, arg in enumerate(expr.items[1:]):
                if i < 2:
                    p = self._extract_proof(arg)
                    if p:
                        premises.append(p)
                else:
                    conclusion = arg
            return ProofNode(rule='mp', conclusion=conclusion, premises=premises, raw=expr)

        elif rule == 'rewrite':
            # (rewrite (= old new))
            if len(expr.items) >= 2:
                eq = expr.items[1]
                return ProofNode(rule='rewrite', conclusion=eq, raw=expr)
            return None

        elif rule == 'monotonicity':
            # (monotonicity proof1 ... (= f(a) f(b)))
            premises = []
            conclusion = None
            for arg in expr.items[1:]:
                p = self._extract_proof(arg)
                if p:
                    premises.append(p)
                elif isinstance(arg, SList):
                    conclusion = arg
            return ProofNode(rule='monotonicity', conclusion=conclusion, premises=premises, raw=expr)

        elif rule == 'quant-inst' or rule.startswith('(_ quant-inst'):
            # ((_ quant-inst val1 val2 ...) result)
            # Extract instantiation values
            args = []
            if rule.startswith('(_ quant-inst'):
                # Parse from the (_ quant-inst ...) form
                if isinstance(head, SList):
                    args = [self._expr_to_string(a) for a in head.items[2:]]
            else:
                args = [self._expr_to_string(a) for a in expr.items[1:-1]]
            conclusion = expr.items[-1] if len(expr.items) > 1 else None
            return ProofNode(rule='quant-inst', conclusion=conclusion, args=args, raw=expr)

        elif rule == 'asserted':
            # (asserted fact)
            if len(expr.items) >= 2:
                return ProofNode(rule='asserted', conclusion=expr.items[1], raw=expr)
            return None

        elif rule == 'unit-resolution':
            # (unit-resolution proof1 proof2 ... result)
            premises = []
            for arg in expr.items[1:-1]:
                p = self._extract_proof(arg)
                if p:
                    premises.append(p)
            conclusion = expr.items[-1] if len(expr.items) > 1 else None
            return ProofNode(rule='unit-resolution', conclusion=conclusion, premises=premises, raw=expr)

        elif rule == 'symm':
            # (symm proof) - symmetry
            if len(expr.items) >= 2:
                p = self._extract_proof(expr.items[1])
                return ProofNode(rule='symm', conclusion=None, premises=[p] if p else [], raw=expr)
            return None

        elif rule == 'lemma':
            # (lemma proof conclusion)
            if len(expr.items) >= 2:
                p = self._extract_proof(expr.items[1])
                conclusion = expr.items[2] if len(expr.items) > 2 else None
                return ProofNode(rule='lemma', conclusion=conclusion, premises=[p] if p else [], raw=expr)
            return None

        # Default: try to extract sub-proofs
        premises = []
        for arg in expr.items[1:]:
            p = self._extract_proof(arg)
            if p:
                premises.append(p)
        if premises:
            return ProofNode(rule=rule, conclusion=None, premises=premises, raw=expr)

        return None

    def _expr_to_string(self, expr: SExpr) -> str:
        """Convert an expression to a readable string."""
        if isinstance(expr, Atom):
            val = expr.value
            # Try to resolve from name map
            if val in self.name_map:
                return self.name_map[val]
            # Try to resolve from bindings
            if val.startswith('?') and val in self.bindings:
                return self._expr_to_string(self.bindings[val])
            return val

        if isinstance(expr, SList):
            if len(expr.items) == 0:
                return "()"
            head = expr.items[0]
            if isinstance(head, Atom):
                # Handle known functions
                if head.value in self.name_map:
                    func = self.name_map[head.value]
                    args = [self._expr_to_string(a) for a in expr.items[1:]]
                    return f"{func}({', '.join(args)})"
            # Generic list
            return f"({' '.join(self._expr_to_string(x) for x in expr.items)})"

        return str(expr)

    def find_equality_chain(self, node: ProofNode) -> List[Tuple[str, str, str]]:
        """Extract a chain of equalities from trans/trans* nodes.

        Returns list of (lhs, rhs, justification) tuples.
        """
        chain = []

        if node.rule in ('trans', 'trans*'):
            for premise in node.premises:
                chain.extend(self.find_equality_chain(premise))
        elif node.rule == 'rewrite':
            if node.conclusion and isinstance(node.conclusion, SList):
                if len(node.conclusion.items) >= 3:
                    lhs = self._expr_to_string(node.conclusion.items[1])
                    rhs = self._expr_to_string(node.conclusion.items[2])
                    chain.append((lhs, rhs, 'rewrite'))
        elif node.rule == 'monotonicity':
            if node.conclusion and isinstance(node.conclusion, SList):
                if len(node.conclusion.items) >= 3:
                    lhs = self._expr_to_string(node.conclusion.items[1])
                    rhs = self._expr_to_string(node.conclusion.items[2])
                    chain.append((lhs, rhs, 'monotonicity'))
        elif node.rule == 'quant-inst':
            chain.append(('', '', f'quant-inst({", ".join(node.args)})'))

        return chain

    def format_proof_chain(self, node: ProofNode, indent: str = "") -> str:
        """Format a proof node as a readable string."""
        lines = []

        lines.append(f"{indent}{node.rule}")

        if node.args:
            lines.append(f"{indent}  args: {node.args}")

        if node.conclusion:
            concl_str = self._expr_to_string(node.conclusion)
            if len(concl_str) > 80:
                concl_str = concl_str[:77] + "..."
            lines.append(f"{indent}  conclusion: {concl_str}")

        for i, premise in enumerate(node.premises):
            lines.append(f"{indent}  premise {i+1}:")
            lines.append(self.format_proof_chain(premise, indent + "    "))

        return "\n".join(lines)


def extract_sum_proof_chain(proof_text: str, name_map: Dict[str, str]) -> Optional[str]:
    """Extract the proof chain for Sum function from Z3 proof output.

    Returns a formatted calc block showing the reasoning.
    """
    # Parse the proof
    proof_sexpr = parse_sexpr(proof_text)
    if not proof_sexpr:
        return None

    extractor = ProofChainExtractor(name_map)
    root = extractor.extract(proof_sexpr)

    if not root:
        return None

    # Find quant-inst nodes for Sum
    def find_sum_insts(node: ProofNode) -> List[ProofNode]:
        results = []
        if node.rule == 'quant-inst':
            # Check if this looks like a Sum instantiation
            for arg in node.args:
                if 'Seq#Take' in arg or 's[..' in arg:
                    results.append(node)
                    break
        for p in node.premises:
            results.extend(find_sum_insts(p))
        return results

    sum_insts = find_sum_insts(root)

    if sum_insts:
        lines = ["// Sum instantiations found in Z3 proof:"]
        for inst in sum_insts:
            lines.append(f"//   quant-inst with: {inst.args}")
        return "\n".join(lines)

    return None
