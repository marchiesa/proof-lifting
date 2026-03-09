"""Extract proof steps from Z3 proof traces."""

from dataclasses import dataclass, field
from typing import List, Dict, Optional, Union, Any
from enum import Enum, auto

try:
    from .sexpr_parser import SExpr, Atom, SList, parse_sexpr
except ImportError:
    from sexpr_parser import SExpr, Atom, SList, parse_sexpr


class ProofRuleType(Enum):
    """Types of Z3 proof rules."""
    FARKAS = auto()          # Linear arithmetic via Farkas lemma
    QUANT_INST = auto()      # Quantifier instantiation
    TRANS = auto()           # Transitivity of equality
    TRANS_STAR = auto()      # Chained transitivity
    SYMM = auto()            # Symmetry of equality
    MP = auto()              # Modus ponens
    UNIT_RESOLUTION = auto() # Unit resolution
    MONOTONICITY = auto()    # Congruence/monotonicity
    REWRITE = auto()         # Term rewriting
    ASSERTED = auto()        # Asserted fact
    DEF_AXIOM = auto()       # Definitional axiom
    LEMMA = auto()           # General lemma
    TH_LEMMA_ARITH = auto()  # Arithmetic theory lemma
    IMPLIES = auto()         # Implication step
    UNKNOWN = auto()         # Unknown rule


@dataclass
class ProofStep:
    """A single proof step."""
    rule: ProofRuleType
    conclusion: Any  # The proved fact
    premises: List[Any] = field(default_factory=list)
    arguments: List[Any] = field(default_factory=list)  # Rule-specific args
    raw: Optional[SExpr] = None

    def __repr__(self):
        return f"ProofStep({self.rule.name}, args={self.arguments})"


@dataclass
class FarkasProof:
    """A Farkas lemma proof with coefficients and constraints."""
    coefficients: List[float]
    constraints: List[Any]  # References to constraint expressions
    raw_constraints: List[str] = field(default_factory=list)  # Human-readable

    def __repr__(self):
        return f"Farkas(coeffs={self.coefficients})"


@dataclass
class QuantInstProof:
    """A quantifier instantiation with the witness values."""
    quantifier_id: Optional[str]
    instantiation_values: List[Any]
    result: Any

    def __repr__(self):
        return f"QuantInst(values={self.instantiation_values})"


@dataclass
class EqualityChain:
    """A chain of equalities from trans*."""
    terms: List[Any]  # a = b = c = ...
    justifications: List[Any]  # Why each step holds

    def __repr__(self):
        return f"EqualityChain({len(self.terms)} terms)"


@dataclass 
class ModusPonens:
    """A modus ponens step: from P and P→Q, derive Q."""
    antecedent: Any  # P
    implication: Any  # P → Q
    consequent: Any  # Q

    def __repr__(self):
        return f"MP({self.antecedent} → {self.consequent})"


@dataclass
class ArithmeticLemma:
    """An arithmetic theory lemma."""
    lemma_type: str  # "farkas", "assign-bounds", etc.
    constraints: List[Any]
    coefficients: List[float] = field(default_factory=list)

    def __repr__(self):
        return f"ArithLemma({self.lemma_type})"


class ProofExtractor:
    """Extract structured proof steps from Z3 proof output."""

    def __init__(self):
        self.let_bindings: Dict[str, SExpr] = {}
        self.proof_steps: List[ProofStep] = []
        self.named_proofs: Dict[str, ProofStep] = {}

    def extract(self, proof_sexpr: SExpr) -> List[ProofStep]:
        """Extract proof steps from a Z3 proof S-expression."""
        self.let_bindings = {}
        self.proof_steps = []
        self.named_proofs = {}

        self._extract_recursive(proof_sexpr)
        return self.proof_steps

    def _extract_recursive(self, expr: SExpr) -> Optional[ProofStep]:
        """Recursively extract proof steps."""
        if isinstance(expr, Atom):
            # Could be a reference to a named proof
            name = expr.value
            if name.startswith('@'):
                return self.named_proofs.get(name)
            return None

        if not isinstance(expr, SList) or not expr.items:
            return None

        head = expr.items[0]

        # Handle nested lists - but not parameterized rules like (_ th-lemma ...)
        if isinstance(head, SList):
            # Check if this is a parameterized rule (starts with _)
            if head.items and isinstance(head.items[0], Atom) and head.items[0].value == "_":
                # This is a parameterized rule, parse it and add to steps
                step = self._parse_proof_rule(expr)
                if step:
                    self.proof_steps.append(step)
                return step
            else:
                # This is a nested list wrapper, recurse into it
                return self._extract_recursive(head)

        if not isinstance(head, Atom):
            return None

        op = head.value

        # Handle 'proof' wrapper - extract from the body
        if op == "proof":
            if len(expr.items) > 1:
                return self._extract_recursive(expr.items[1])
            return None

        # Handle let bindings
        if op == "let":
            return self._handle_let(expr)

        # Handle proof rules
        step = self._parse_proof_rule(expr)
        if step:
            self.proof_steps.append(step)

            # If this is a named proof (bound by let), store it
            # Names are handled in _handle_let

        # IMPORTANT: Also recursively extract from all subexpressions
        # This catches quant-inst nested inside mp, unit-resolution, etc.
        for item in expr.items[1:]:
            if isinstance(item, SList):
                self._extract_recursive(item)

        return step

    def _handle_let(self, expr: SList) -> Optional[ProofStep]:
        """Handle let bindings and extract the body."""
        # (let ((name value) ...) body)
        if len(expr.items) < 3:
            return None

        bindings = expr.items[1]
        body = expr.items[2]

        # Process bindings
        if isinstance(bindings, SList):
            for binding in bindings.items:
                if isinstance(binding, SList) and len(binding.items) >= 2:
                    name_expr = binding.items[0]
                    value_expr = binding.items[1]

                    if isinstance(name_expr, Atom):
                        name = name_expr.value
                        self.let_bindings[name] = value_expr

                        # If it's a proof step, also store it
                        if name.startswith('@'):
                            step = self._extract_recursive(value_expr)
                            if step:
                                self.named_proofs[name] = step

        # Extract from body
        return self._extract_recursive(body)

    def _parse_proof_rule(self, expr: SList) -> Optional[ProofStep]:
        """Parse a proof rule application."""
        if not expr.items:
            return None

        head = expr.items[0]

        # Handle (_ rule-name args...) syntax
        if isinstance(head, SList) and head.items:
            if isinstance(head.items[0], Atom) and head.items[0].value == "_":
                return self._parse_parameterized_rule(expr)

        if not isinstance(head, Atom):
            return None

        op = head.value

        # Dispatch to specific handlers
        handlers = {
            "th-lemma": self._parse_th_lemma,
            "quant-inst": self._parse_quant_inst,
            "trans": self._parse_trans,
            "trans*": self._parse_trans_star,
            "symm": self._parse_symm,
            "mp": self._parse_mp,
            "unit-resolution": self._parse_unit_resolution,
            "monotonicity": self._parse_monotonicity,
            "rewrite": self._parse_rewrite,
            "asserted": self._parse_asserted,
            "def-axiom": self._parse_def_axiom,
            "lemma": self._parse_lemma,
            "=>": self._parse_implication,
        }

        handler = handlers.get(op)
        if handler:
            return handler(expr)

        return None

    def _parse_parameterized_rule(self, expr: SList) -> Optional[ProofStep]:
        """Parse (_ rule-name params...) application."""
        head = expr.items[0]  # (_ rule-name params...)

        if not isinstance(head, SList) or len(head.items) < 2:
            return None

        rule_name = head.items[1]
        if not isinstance(rule_name, Atom):
            return None

        if rule_name.value == "quant-inst":
            return self._parse_quant_inst_parameterized(expr, head)
        elif rule_name.value == "th-lemma":
            return self._parse_th_lemma_parameterized(expr, head)

        return None

    def _parse_th_lemma(self, expr: SList) -> Optional[ProofStep]:
        """Parse (th-lemma theory-name ...) proof."""
        if len(expr.items) < 2:
            return None

        theory = expr.items[1]
        if isinstance(theory, Atom) and theory.value == "arith":
            return self._parse_arith_lemma(expr)

        return ProofStep(
            rule=ProofRuleType.LEMMA,
            conclusion=expr,
            raw=expr
        )

    def _parse_th_lemma_parameterized(self, expr: SList, head: SList) -> Optional[ProofStep]:
        """Parse (_ th-lemma arith farkas c1 c2 ...) proof."""
        # head = (_ th-lemma arith farkas c1 c2 ...)
        # expr.items[1:] are the constraints

        if len(head.items) < 4:
            return None

        theory = head.items[2]
        if not isinstance(theory, Atom) or theory.value != "arith":
            return None

        lemma_type = head.items[3]
        if isinstance(lemma_type, Atom) and lemma_type.value == "farkas":
            # Extract Farkas coefficients
            coefficients = []
            for i in range(4, len(head.items)):
                coef = head.items[i]
                if isinstance(coef, Atom):
                    try:
                        coefficients.append(float(coef.value))
                    except ValueError:
                        pass

            # Constraints are the remaining arguments
            constraints = list(expr.items[1:-1])  # Exclude 'false' at end

            farkas = FarkasProof(
                coefficients=coefficients,
                constraints=constraints
            )

            arith_lemma = ArithmeticLemma(
                lemma_type="farkas",
                constraints=constraints,
                coefficients=coefficients
            )

            return ProofStep(
                rule=ProofRuleType.FARKAS,
                conclusion=Atom("false"),
                arguments=[farkas, arith_lemma],
                premises=constraints,
                raw=expr
            )

        # Handle other arithmetic lemma types
        lemma_type_str = lemma_type.value if isinstance(lemma_type, Atom) else "unknown"
        arith_lemma = ArithmeticLemma(
            lemma_type=lemma_type_str,
            constraints=list(expr.items[1:])
        )

        return ProofStep(
            rule=ProofRuleType.TH_LEMMA_ARITH,
            conclusion=expr,
            arguments=[arith_lemma],
            raw=expr
        )

    def _parse_arith_lemma(self, expr: SList) -> Optional[ProofStep]:
        """Parse arithmetic theory lemma."""
        return ProofStep(
            rule=ProofRuleType.TH_LEMMA_ARITH,
            conclusion=expr,
            raw=expr
        )

    def _parse_quant_inst(self, expr: SList) -> Optional[ProofStep]:
        """Parse quantifier instantiation."""
        # (quant-inst values... result)
        values = [x for x in expr.items[1:]]

        return ProofStep(
            rule=ProofRuleType.QUANT_INST,
            conclusion=expr,
            arguments=values,
            raw=expr
        )

    def _parse_quant_inst_parameterized(self, expr: SList, head: SList) -> Optional[ProofStep]:
        """Parse (_ quant-inst v1 v2 ...) proof."""
        # head = (_ quant-inst v1 v2 ...)
        values = list(head.items[2:])  # Skip _ and quant-inst

        # The result is typically the first argument after head
        result = expr.items[1] if len(expr.items) > 1 else None

        qi = QuantInstProof(
            quantifier_id=None,
            instantiation_values=values,
            result=result
        )

        return ProofStep(
            rule=ProofRuleType.QUANT_INST,
            conclusion=result,
            arguments=[qi],
            raw=expr
        )

    def _parse_trans(self, expr: SList) -> Optional[ProofStep]:
        """Parse transitivity proof."""
        premises = list(expr.items[1:])
        return ProofStep(
            rule=ProofRuleType.TRANS,
            conclusion=expr,
            premises=premises,
            raw=expr
        )

    def _parse_trans_star(self, expr: SList) -> Optional[ProofStep]:
        """Parse chained transitivity proof."""
        premises = list(expr.items[1:])

        chain = EqualityChain(
            terms=[],  # Would need to extract from premises
            justifications=premises
        )

        return ProofStep(
            rule=ProofRuleType.TRANS_STAR,
            conclusion=expr,
            arguments=[chain],
            premises=premises,
            raw=expr
        )

    def _parse_symm(self, expr: SList) -> Optional[ProofStep]:
        """Parse symmetry proof."""
        premise = expr.items[1] if len(expr.items) > 1 else None
        return ProofStep(
            rule=ProofRuleType.SYMM,
            conclusion=expr,
            premises=[premise] if premise else [],
            raw=expr
        )

    def _parse_mp(self, expr: SList) -> Optional[ProofStep]:
        """Parse modus ponens proof."""
        # (mp proof-of-P proof-of-P→Q result-Q)
        premises = list(expr.items[1:])
        
        mp_proof = None
        if len(premises) >= 2:
            mp_proof = ModusPonens(
                antecedent=premises[0],
                implication=premises[1],
                consequent=premises[-1] if len(premises) > 2 else None
            )
        
        return ProofStep(
            rule=ProofRuleType.MP,
            conclusion=expr,
            premises=premises,
            arguments=[mp_proof] if mp_proof else [],
            raw=expr
        )

    def _parse_implication(self, expr: SList) -> Optional[ProofStep]:
        """Parse implication expression."""
        # (=> antecedent consequent)
        if len(expr.items) >= 3:
            return ProofStep(
                rule=ProofRuleType.IMPLIES,
                conclusion=expr.items[2],
                premises=[expr.items[1]],
                raw=expr
            )
        return None

    def _parse_unit_resolution(self, expr: SList) -> Optional[ProofStep]:
        """Parse unit resolution proof."""
        premises = list(expr.items[1:])
        return ProofStep(
            rule=ProofRuleType.UNIT_RESOLUTION,
            conclusion=expr,
            premises=premises,
            raw=expr
        )

    def _parse_monotonicity(self, expr: SList) -> Optional[ProofStep]:
        """Parse monotonicity/congruence proof."""
        premises = list(expr.items[1:])
        return ProofStep(
            rule=ProofRuleType.MONOTONICITY,
            conclusion=expr,
            premises=premises,
            raw=expr
        )

    def _parse_rewrite(self, expr: SList) -> Optional[ProofStep]:
        """Parse rewrite proof."""
        arg = expr.items[1] if len(expr.items) > 1 else None
        return ProofStep(
            rule=ProofRuleType.REWRITE,
            conclusion=arg,
            raw=expr
        )

    def _parse_asserted(self, expr: SList) -> Optional[ProofStep]:
        """Parse asserted fact."""
        fact = expr.items[1] if len(expr.items) > 1 else None
        return ProofStep(
            rule=ProofRuleType.ASSERTED,
            conclusion=fact,
            raw=expr
        )

    def _parse_def_axiom(self, expr: SList) -> Optional[ProofStep]:
        """Parse definitional axiom."""
        axiom = expr.items[1] if len(expr.items) > 1 else None
        return ProofStep(
            rule=ProofRuleType.DEF_AXIOM,
            conclusion=axiom,
            raw=expr
        )

    def _parse_lemma(self, expr: SList) -> Optional[ProofStep]:
        """Parse lemma proof.

        A lemma often wraps another proof, e.g.:
        (lemma ((_ th-lemma arith farkas c1 c2 ...) constraint1 ... false) result)
        """
        # Check if there's an inner Farkas proof
        if len(expr.items) >= 2:
            inner = expr.items[1]
            if isinstance(inner, SList) and len(inner.items) >= 1:
                inner_head = inner.items[0]
                # Check for (_ th-lemma arith farkas ...)
                if isinstance(inner_head, SList) and len(inner_head.items) >= 4:
                    if (isinstance(inner_head.items[0], Atom) and
                        inner_head.items[0].value == "_" and
                        isinstance(inner_head.items[1], Atom) and
                        inner_head.items[1].value == "th-lemma"):
                        # This is a wrapped Farkas lemma - parse it and add to steps
                        farkas_step = self._parse_th_lemma_parameterized(inner, inner_head)
                        if farkas_step:
                            self.proof_steps.append(farkas_step)
                            return farkas_step

        return ProofStep(
            rule=ProofRuleType.LEMMA,
            conclusion=expr,
            raw=expr
        )

    def get_farkas_proofs(self) -> List[FarkasProof]:
        """Get all Farkas lemma proofs."""
        result = []
        for step in self.proof_steps:
            if step.rule == ProofRuleType.FARKAS:
                for arg in step.arguments:
                    if isinstance(arg, FarkasProof):
                        result.append(arg)
        return result

    def get_quant_instantiations(self) -> List[QuantInstProof]:
        """Get all quantifier instantiations."""
        result = []
        for step in self.proof_steps:
            if step.rule == ProofRuleType.QUANT_INST:
                for arg in step.arguments:
                    if isinstance(arg, QuantInstProof):
                        result.append(arg)
        return result

    def format_quant_inst(self, qi: QuantInstProof, var_map: Dict[str, str]) -> str:
        """Format a quantifier instantiation with readable names."""
        values = []
        for v in qi.instantiation_values:
            values.append(self.expr_to_string(v, var_map))
        return f"Instantiated with: {', '.join(values)}"

    def get_function_instantiations(self, var_map: Dict[str, str],
                                     function_names: List[str] = None) -> List[Dict]:
        """Get quant-inst steps that instantiate specific functions.

        Returns a list of dicts with:
          - 'function': the function name
          - 'args': the instantiation arguments
          - 'readable': human-readable form
        """
        if function_names is None:
            function_names = ['Sum', 'Seq#Length', 'Seq#Take', 'Seq#Index']

        results = []
        for step in self.proof_steps:
            if step.rule == ProofRuleType.QUANT_INST:
                for arg in step.arguments:
                    if isinstance(arg, QuantInstProof):
                        # Check if any instantiation value references a target function
                        for v in arg.instantiation_values:
                            v_str = self.expr_to_string(v, var_map)
                            for fn in function_names:
                                if fn in v_str or fn.lower() in v_str.lower():
                                    results.append({
                                        'function': fn,
                                        'args': [self.expr_to_string(x, var_map)
                                                for x in arg.instantiation_values],
                                        'readable': self.format_quant_inst(arg, var_map),
                                        'raw': arg
                                    })
                                    break
        return results

    def get_sum_unfoldings(self, var_map: Dict[str, str]) -> List[Dict]:
        """Extract Sum function unfoldings from quant-inst steps.

        The Sum axiom has the form:
            forall ls, s :: Sum(ls, s) == if |s| == 0 then 0 else Sum(ls', s[..|s|-1]) + s[|s|-1]

        Returns list of dicts with:
          - 'call': the Sum call being unfolded (e.g., 'Sum(s[..i])')
          - 'result': what it unfolds to (e.g., 'Sum(s[..i-1]) + s[i-1]')
          - 'sequence': the sequence argument
          - 'raw': the raw QuantInstProof
        """
        results = []

        for step in self.proof_steps:
            if step.rule != ProofRuleType.QUANT_INST:
                continue

            for arg in step.arguments:
                if not isinstance(arg, QuantInstProof):
                    continue

                # Check if this looks like a Sum axiom instantiation
                # Sum axiom has 2 args: layer (like $LS($LZ)) and sequence
                values = arg.instantiation_values
                if len(values) != 2:
                    continue

                # First arg should contain $LS or layer pattern
                first_str = self.expr_to_string(values[0], var_map)
                if '$LS' not in first_str and 'LayerType' not in first_str:
                    continue

                # Second arg is the sequence
                seq_str = self.expr_to_string(values[1], var_map)

                # Try to format as a Sum call unfolding
                results.append({
                    'call': f'Sum({seq_str})',
                    'sequence': seq_str,
                    'layer': first_str,
                    'raw': arg
                })

        return results

    def generate_sum_calc_block(self, sum_unfoldings: List[Dict],
                                 indent: str = "    ") -> str:
        """Generate a Dafny calc block for Sum function unfoldings.

        Given unfoldings like Sum(s[..i]), generates BOTH:
        1. Forward unfolding: Sum(s[..i]) == Sum(s[..i-1]) + s[i-1]
        2. Backward folding: Sum(s[..i]) + s[i] == Sum(s[..i+1])

        The backward form is often more useful for loop invariant maintenance.
        """
        if not sum_unfoldings:
            return ""

        import re
        blocks = []

        for unf in sum_unfoldings:
            seq = unf['sequence']

            # Match patterns like s[..i], s[..i+1], s[..n-1]
            match = re.match(r'^(\w+)\[\.\.(.+)\]$', seq)

            if not match:
                continue

            base_seq = match.group(1)  # e.g., 's'
            index_expr = match.group(2)  # e.g., 'i', 'i+1', 'n-1'

            # Generate forward unfolding calc block
            # Sum(s[..i]) == Sum(s[..i-1]) + s[i-1]
            lines = [f"{indent}// Forward: unfold Sum({seq})"]
            lines.append(f"{indent}calc {{")
            lines.append(f"{indent}    Sum({seq});")
            lines.append(f"{indent}    == {{ unfold Sum definition: Sum(s) == Sum(s[..|s|-1]) + s[|s|-1] }}")

            # Compute the unfolded form
            if index_expr.isalnum():
                prev_index = f"{index_expr} - 1"
            elif '+' in index_expr:
                parts = index_expr.split('+')
                if len(parts) == 2 and parts[1].strip().isdigit():
                    var = parts[0].strip()
                    num = int(parts[1].strip())
                    prev_index = var if num == 1 else f"{var} + {num - 1}"
                else:
                    prev_index = f"({index_expr}) - 1"
            else:
                prev_index = f"({index_expr}) - 1"

            lines.append(f"{indent}    Sum({base_seq}[..{prev_index}]) + {base_seq}[{prev_index}];")
            lines.append(f"{indent}}}")
            blocks.append("\n".join(lines))

            # Generate backward folding calc block (more useful for loop invariants)
            # Sum(s[..i]) + s[i] == Sum(s[..i+1])
            lines = [f"{indent}// Backward: fold into Sum({base_seq}[..{index_expr} + 1])"]
            lines.append(f"{indent}calc {{")
            lines.append(f"{indent}    Sum({seq}) + {base_seq}[{index_expr}];")
            lines.append(f"{indent}    == {{ fold Sum: Sum(s[..n-1]) + s[n-1] == Sum(s[..n]) }}")

            # Compute the folded form
            if index_expr.isalnum():
                next_index = f"{index_expr} + 1"
            elif '-' in index_expr and not index_expr.startswith('-'):
                # Like 'i - 1' -> becomes 'i'
                parts = index_expr.split('-')
                if len(parts) == 2 and parts[1].strip().isdigit():
                    var = parts[0].strip()
                    num = int(parts[1].strip())
                    next_index = var if num == 1 else f"{var} - {num - 1}"
                else:
                    next_index = f"({index_expr}) + 1"
            else:
                next_index = f"{index_expr} + 1"

            lines.append(f"{indent}    Sum({base_seq}[..{next_index}]);")
            lines.append(f"{indent}}}")
            blocks.append("\n".join(lines))

        return "\n\n".join(blocks)

    def get_sequence_axiom_uses(self, var_map: Dict[str, str]) -> List[Dict]:
        """Extract sequence axiom instantiations (Seq#Length, Seq#Take, etc).

        Returns list of dicts with:
          - 'axiom': the axiom being used
          - 'args': the instantiation arguments
          - 'readable': human-readable description
        """
        results = []

        # Map from number of args to likely axiom types
        axiom_patterns = {
            1: ['Seq#Length'],  # |s|
            2: ['Seq#Take', 'Seq#Drop', 'Seq#Index'],  # s[..i], s[i..], s[i]
            3: ['Seq#Update'],  # s[i := v]
        }

        for step in self.proof_steps:
            if step.rule != ProofRuleType.QUANT_INST:
                continue

            for arg in step.arguments:
                if not isinstance(arg, QuantInstProof):
                    continue

                values = arg.instantiation_values
                args_str = [self.expr_to_string(v, var_map) for v in values]

                # Check the result to determine which axiom
                result_str = ""
                if arg.result:
                    result_str = self.expr_to_string(arg.result, var_map)

                # Detect Seq#Take axiom: instantiated with (seq, int)
                if len(values) == 2:
                    # Check if second arg looks like an integer
                    second = args_str[1]
                    if second.isdigit() or 'i' in second or '+' in second or '-' in second:
                        # Could be Seq#Take
                        if 'Seq#Take' in result_str or 'Seq#Length' in result_str:
                            readable = f'{args_str[0]}[..{args_str[1]}]'
                            results.append({
                                'axiom': 'Seq#Take',
                                'args': args_str,
                                'readable': readable
                            })

        return results

    def get_equality_chains(self) -> List[EqualityChain]:
        """Get all equality chains from trans*."""
        result = []
        for step in self.proof_steps:
            if step.rule == ProofRuleType.TRANS_STAR:
                for arg in step.arguments:
                    if isinstance(arg, EqualityChain):
                        result.append(arg)
        return result

    def get_modus_ponens(self) -> List[ModusPonens]:
        """Get all modus ponens steps."""
        result = []
        for step in self.proof_steps:
            if step.rule == ProofRuleType.MP:
                for arg in step.arguments:
                    if isinstance(arg, ModusPonens):
                        result.append(arg)
        return result

    def get_arithmetic_lemmas(self) -> List[ArithmeticLemma]:
        """Get all arithmetic lemmas."""
        result = []
        for step in self.proof_steps:
            if step.rule in (ProofRuleType.FARKAS, ProofRuleType.TH_LEMMA_ARITH):
                for arg in step.arguments:
                    if isinstance(arg, ArithmeticLemma):
                        result.append(arg)
        return result

    def resolve_reference(self, ref: Any, depth: int = 0) -> Any:
        """Resolve a reference (@xNNN or ?xNNN) through let bindings."""
        if depth > 50:  # Prevent infinite recursion
            return ref

        if isinstance(ref, Atom):
            name = ref.value
            # Check if it's a let-bound name
            if name in self.let_bindings:
                return self.resolve_reference(self.let_bindings[name], depth + 1)
            return ref
        elif isinstance(ref, SList):
            # Recursively resolve list elements
            resolved_items = []
            for item in ref.items:
                resolved_items.append(self.resolve_reference(item, depth + 1))
            return SList(resolved_items)
        return ref

    def expr_to_string(self, expr: Any, var_map: Optional[Dict[str, str]] = None) -> str:
        """Convert a Z3 expression to a human-readable string."""
        if var_map is None:
            var_map = {}

        if isinstance(expr, Atom):
            value = expr.value
            # Check variable mapping
            if value in var_map:
                return var_map[value]
            # Check if it's a let-bound variable, resolve it
            if value in self.let_bindings:
                return self.expr_to_string(self.let_bindings[value], var_map)
            # Check if it's a number
            try:
                return str(int(value))
            except ValueError:
                pass
            try:
                return str(float(value))
            except ValueError:
                pass
            return value

        elif isinstance(expr, SList):
            if not expr.items:
                return "()"

            head = expr.items[0]
            if isinstance(head, Atom):
                op = head.value

                # Proof operations - extract the constraint they prove
                if op in ("and-elim", "not-or-elim"):
                    if len(expr.items) >= 3:
                        # The constraint expression is typically the last argument
                        return self.expr_to_string(expr.items[-1], var_map)
                    elif len(expr.items) >= 2:
                        return self.expr_to_string(expr.items[1], var_map)
                    return f"{op}(?)"

                # hypothesis - this is a constraint being assumed for contradiction
                elif op == "hypothesis":
                    if len(expr.items) >= 2:
                        return f"HYPO({self.expr_to_string(expr.items[1], var_map)})"
                    return "HYPO(?)"

                # unit-resolution - extract the final derived constraint
                elif op == "unit-resolution":
                    if len(expr.items) >= 2:
                        # Last argument is usually the derived constraint
                        return self.expr_to_string(expr.items[-1], var_map)
                    return "unit-res(?)"

                # lemma - extract the inner proof's conclusion
                elif op == "lemma":
                    if len(expr.items) >= 3:
                        return self.expr_to_string(expr.items[-1], var_map)
                    return "lemma(?)"

                args = [self.expr_to_string(x, var_map) for x in expr.items[1:]]

                # Arithmetic operators
                if op == "+":
                    # Simplify a + -b to a - b
                    simplified = []
                    for arg in args:
                        if arg.startswith('-') and simplified:
                            simplified.append(f"- {arg[1:]}")
                        else:
                            if simplified:
                                simplified.append(f"+ {arg}")
                            else:
                                simplified.append(arg)
                    return " ".join(simplified)
                elif op == "-":
                    if len(args) == 1:
                        return f"-{args[0]}"
                    return " - ".join(args)
                elif op == "*":
                    # Simplify multiplication by -1
                    if len(args) == 2:
                        if args[0] == "-1":
                            return f"-{args[1]}"
                        if args[1] == "-1":
                            return f"-{args[0]}"
                    return " * ".join(args)

                # Comparisons
                elif op == "<=":
                    return f"{args[0]} <= {args[1]}"
                elif op == "<":
                    return f"{args[0]} < {args[1]}"
                elif op == ">=":
                    return f"{args[0]} >= {args[1]}"
                elif op == ">":
                    return f"{args[0]} > {args[1]}"
                elif op == "=":
                    return f"{args[0]} == {args[1]}"

                # Logical operators
                elif op == "not":
                    return f"NOT({args[0]})"
                elif op == "and":
                    return " AND ".join(args)
                elif op == "or":
                    return " OR ".join(args)
                elif op == "=>":
                    return f"{args[0]} ==> {args[1]}"

                # Default: function application
                else:
                    # Resolve function name through var_map
                    resolved_op = var_map.get(op, op) if op.startswith('$generated@@') else op

                    # Handle identity functions (Box, Unbox, LitInt)
                    if resolved_op in ('$Box', '$Unbox', 'LitInt', 'Lit'):
                        if len(args) == 1:
                            return args[0]
                        elif len(args) == 2:
                            # Two-arg Box/Unbox: (Box Type Value) -> Value
                            return args[1]

                    # Check for box/unbox patterns that simplify
                    # $generated@@N($generated@@M(x)) where N is unbox, M is box -> just x
                    if (op.startswith('$generated@@') and len(args) == 1 and
                        args[0].startswith('$generated@@') and '(' in args[0]):
                        # Extract inner: $generated@@M(x) -> x
                        import re
                        inner_match = re.match(r'\$generated@@\d+\((.+)\)', args[0])
                        if inner_match:
                            return inner_match.group(1)

                    # LitInt(0) -> 0
                    if op.startswith('$generated@@') and len(args) == 1:
                        try:
                            int(args[0])
                            return args[0]  # It's a literal, just return the number
                        except ValueError:
                            pass

                    # Format sequence/set operations in Dafny syntax
                    if resolved_op == 'Seq#Length' and len(args) == 1:
                        return f"|{args[0]}|"
                    elif resolved_op == 'Seq#Index' and len(args) == 2:
                        return f"{args[0]}[{args[1]}]"
                    elif resolved_op == 'Seq#Update' and len(args) == 3:
                        return f"{args[0]}[{args[1]} := {args[2]}]"
                    elif resolved_op == 'Seq#Append' and len(args) == 2:
                        return f"{args[0]} + {args[1]}"
                    elif resolved_op == 'Seq#Take' and len(args) == 2:
                        return f"{args[0]}[..{args[1]}]"
                    elif resolved_op == 'Seq#Drop' and len(args) == 2:
                        return f"{args[0]}[{args[1]}..]"
                    elif resolved_op == 'Set#Card' and len(args) == 1:
                        return f"|{args[0]}|"
                    elif resolved_op == 'Set#Union' and len(args) == 2:
                        return f"{args[0]} + {args[1]}"
                    elif resolved_op == 'Set#Intersection' and len(args) == 2:
                        return f"{args[0]} * {args[1]}"
                    elif resolved_op == 'Seq#Empty' and len(args) == 0:
                        return "[]"

                    return f"{resolved_op}({', '.join(args)})"

        return str(expr)

    def get_resolved_farkas_constraints(self, farkas: FarkasProof,
                                        var_map: Optional[Dict[str, str]] = None) -> List[str]:
        """Get human-readable constraints from a Farkas proof."""
        result = []
        for constraint in farkas.constraints:
            resolved = self.resolve_reference(constraint)
            readable = self.expr_to_string(resolved, var_map)
            result.append(readable)
        return result

    def extract_farkas_goal(self, farkas: FarkasProof,
                            var_map: Optional[Dict[str, str]] = None) -> Optional[str]:
        """Extract the goal being proved by a Farkas lemma.

        The goal is the negation of the hypothesis constraint. We look for:
        1. HYPO(NOT(x - y <= 0)) -> goal is x <= y
        2. HYPO(x - y >= 0) -> goal is x <= y (negating "x >= y" gives "x < y", close enough)
        3. NOT(x - y <= 0) constraints

        Returns the goal in simplified form (e.g., 'a <= c').
        """
        import re

        constraints = self.get_resolved_farkas_constraints(farkas, var_map)

        for i, constraint in enumerate(constraints):
            # Look for hypothesis - the hypothesis IS the negated goal
            if 'HYPO(' in constraint:
                # HYPO(NOT(a - c <= 0)) means hypothesis is "NOT(a <= c)" so goal is "a <= c"
                match = re.search(r'HYPO\(NOT\((.+?)\)\)', constraint)
                if match:
                    inner = match.group(1)
                    # inner is like "a - c <= 0", goal is "a <= c"
                    simp = self._simplify_inequality(inner)
                    if simp:
                        return simp

                # HYPO(a - c >= 0) means hypothesis is "a >= c" so goal is "a <= c"
                match = re.search(r'HYPO\(([^)]+)\s*>=\s*0\)', constraint)
                if match:
                    inner = match.group(1).strip()
                    # inner is like "a - c", goal is "a <= c"
                    var_match = re.match(r'^(\w+)\s*-\s*(\w+)$', inner)
                    if var_match:
                        return f"{var_match.group(1)} <= {var_match.group(2)}"
                    var_match = re.match(r'^(\w+)\s*\+\s*-(\w+)$', inner)
                    if var_match:
                        return f"{var_match.group(1)} <= {var_match.group(2)}"

        # Fallback: look for NOT(...) constraints (negated goals)
        for i, constraint in enumerate(constraints):
            if constraint.startswith('NOT('):
                inner = constraint[4:-1]  # Remove NOT( and )
                simp = self._simplify_inequality(inner)
                if simp:
                    return simp

        return None

    def _simplify_inequality(self, expr: str) -> Optional[str]:
        """Simplify an inequality expression to readable form."""
        import re

        # "a - c <= 0" -> "a <= c"
        match = re.match(r'^(\w+)\s*-\s*(\w+)\s*<=\s*0$', expr.strip())
        if match:
            return f"{match.group(1)} <= {match.group(2)}"

        # "a - c >= 0" -> "a >= c"
        match = re.match(r'^(\w+)\s*-\s*(\w+)\s*>=\s*0$', expr.strip())
        if match:
            return f"{match.group(1)} >= {match.group(2)}"

        # "a + -c <= 0" -> "a <= c"
        match = re.match(r'^(\w+)\s*\+\s*-(\w+)\s*<=\s*0$', expr.strip())
        if match:
            return f"{match.group(1)} <= {match.group(2)}"

        # Already simplified: "a <= c"
        match = re.match(r'^(\w+)\s*(<=|>=|<|>)\s*(\w+)$', expr.strip())
        if match:
            return expr.strip()

        return None
