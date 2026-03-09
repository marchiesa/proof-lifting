"""Generate Dafny calc blocks from extracted proofs."""

from dataclasses import dataclass
from typing import List, Dict, Optional, Any
try:
    from .proof_extractor import (
        ProofStep, ProofRuleType, FarkasProof, QuantInstProof, EqualityChain,
        ModusPonens, ArithmeticLemma
    )
    from .name_mapper import NameMapper
except ImportError:
    from proof_extractor import (
        ProofStep, ProofRuleType, FarkasProof, QuantInstProof, EqualityChain,
        ModusPonens, ArithmeticLemma
    )
    from name_mapper import NameMapper


@dataclass
class CalcStep:
    """A single step in a calc block."""
    expression: str
    relation: str  # "==", "<=", "<", ">=", ">", "==>"
    justification: str

    def __repr__(self):
        return f"{self.expression} {self.relation} {{ {self.justification} }}"


@dataclass
class CalcBlock:
    """A complete calc block."""
    steps: List[CalcStep]

    def to_dafny(self, indent: int = 0) -> str:
        """Generate Dafny calc block syntax."""
        ind = "  " * indent
        lines = [f"{ind}calc {{"]

        for i, step in enumerate(self.steps):
            lines.append(f"{ind}  {step.expression};")
            if i < len(self.steps) - 1:
                next_step = self.steps[i + 1]
                lines.append(f"{ind}{next_step.relation} {{ {step.justification} }}")

        lines.append(f"{ind}}}")
        return "\n".join(lines)


@dataclass
class AssertSequence:
    """A sequence of assertions."""
    assertions: List[str]
    justifications: List[str]

    def to_dafny(self, indent: int = 0) -> str:
        """Generate Dafny assert statements."""
        ind = "  " * indent
        lines = []
        for assertion, justification in zip(self.assertions, self.justifications):
            # Handle comments (start with //)
            if assertion.startswith("//"):
                lines.append(f"{ind}{assertion}")
            elif justification:
                lines.append(f"{ind}assert {assertion};  // {justification}")
            else:
                lines.append(f"{ind}assert {assertion};")
        return "\n".join(lines)


@dataclass
class ImplicationChain:
    """A chain of implications for modus ponens."""
    steps: List[tuple]  # [(premise, conclusion), ...]
    
    def to_dafny(self, indent: int = 0) -> str:
        """Generate Dafny calc block with ==> steps."""
        ind = "  " * indent
        lines = [f"{ind}calc ==> {{"]
        
        for premise, conclusion in self.steps:
            lines.append(f"{ind}  {premise};")
            lines.append(f"{ind}==>")
            lines.append(f"{ind}  {conclusion};")
        
        lines.append(f"{ind}}}")
        return "\n".join(lines)


class DafnyGenerator:
    """Generate Dafny proof fragments from extracted proofs."""

    def __init__(self, mapper: Optional[NameMapper] = None):
        self.mapper = mapper or NameMapper()
        self.variable_names: Dict[str, str] = {}  # Z3 var -> Dafny name

    def set_variable_mapping(self, z3_name: str, dafny_name: str):
        """Set a variable name mapping."""
        self.variable_names[z3_name] = dafny_name

    def resolve_name(self, z3_term: Any) -> str:
        """Resolve a Z3 term to a Dafny expression."""
        try:
            from .sexpr_parser import Atom, SList
        except ImportError:
            from sexpr_parser import Atom, SList

        if isinstance(z3_term, Atom):
            value = z3_term.value

            # Check variable mapping
            if value in self.variable_names:
                return self.variable_names[value]

            # Check if it's a generated name
            if value.startswith('$generated@@'):
                return self.mapper.get_dafny_name(value)

            # Check if it's a number
            try:
                return str(int(value))
            except ValueError:
                pass

            return value

        elif isinstance(z3_term, SList):
            if not z3_term.items:
                return "()"

            head = z3_term.items[0]
            if isinstance(head, Atom):
                op = head.value

                # Handle arithmetic
                if op == "+":
                    args = [self.resolve_name(x) for x in z3_term.items[1:]]
                    return " + ".join(args)
                elif op == "-":
                    if len(z3_term.items) == 2:
                        return f"-{self.resolve_name(z3_term.items[1])}"
                    args = [self.resolve_name(x) for x in z3_term.items[1:]]
                    return " - ".join(args)
                elif op == "*":
                    args = [self.resolve_name(x) for x in z3_term.items[1:]]
                    return " * ".join(args)

                # Handle comparisons
                elif op in ["<=", "<", ">=", ">", "="]:
                    left = self.resolve_name(z3_term.items[1])
                    right = self.resolve_name(z3_term.items[2])
                    dafny_op = "==" if op == "=" else op
                    return f"{left} {dafny_op} {right}"

                # Handle implication
                elif op == "=>":
                    left = self.resolve_name(z3_term.items[1])
                    right = self.resolve_name(z3_term.items[2])
                    return f"{left} ==> {right}"

                # Handle logical operators
                elif op == "and":
                    args = [self.resolve_name(x) for x in z3_term.items[1:]]
                    return " && ".join(args)
                elif op == "or":
                    args = [self.resolve_name(x) for x in z3_term.items[1:]]
                    return " || ".join(args)
                elif op == "not":
                    arg = self.resolve_name(z3_term.items[1])
                    return f"!{arg}"

                # Handle sequence operations
                elif op.startswith('$generated@@'):
                    dafny_op = self.mapper.get_dafny_name(op)
                    args = [self.resolve_name(x) for x in z3_term.items[1:]]

                    if dafny_op == "|...|":  # Seq#Length
                        return f"|{args[0]}|"
                    elif dafny_op == "[..]":  # Seq#Take or Seq#Drop
                        return f"{args[0]}[..{args[1]}]"
                    elif dafny_op == "[]":  # Seq#Index
                        return f"{args[0]}[{args[1]}]"
                    else:
                        return f"{dafny_op}({', '.join(args)})"

                # Generic function call
                else:
                    args = [self.resolve_name(x) for x in z3_term.items[1:]]
                    # Check if mapper can format this as Dafny syntax
                    boogie_name = self.mapper.get_boogie_name(op) if op.startswith('$generated@@') else op
                    return self.mapper.format_dafny_call(boogie_name, args)

        return str(z3_term)

    def generate_from_farkas(self, farkas: FarkasProof,
                             constraint_names: Optional[List[str]] = None) -> CalcBlock:
        """Generate a calc block from a Farkas proof."""

        # Without constraint resolution, we show the structure
        steps = []

        # Find non-zero coefficients
        nonzero = [(c, i) for i, c in enumerate(farkas.coefficients) if c != 0]

        if not nonzero:
            return CalcBlock(steps=[])

        # Generate explanation
        steps.append(CalcStep(
            expression="// Farkas certificate",
            relation="",
            justification=f"Coefficients: {farkas.coefficients}"
        ))

        # Show the linear combination structure
        combo_parts = []
        for coef, idx in nonzero:
            constraint_name = f"C{idx+1}"
            if constraint_names and idx < len(constraint_names):
                constraint_name = constraint_names[idx]
            combo_parts.append(f"{coef} × {constraint_name}")

        steps.append(CalcStep(
            expression="// " + " + ".join(combo_parts),
            relation="",
            justification="leads to contradiction"
        ))

        return CalcBlock(steps=steps)

    def generate_from_farkas_detailed(
            self,
            farkas: FarkasProof,
            constraints: List[str]
    ) -> str:
        """Generate detailed Farkas proof explanation."""
        lines = []
        lines.append("// Farkas lemma proof:")
        lines.append(f"// Coefficients: {farkas.coefficients}")
        lines.append("//")
        lines.append("// Linear combination:")
        
        nonzero = [(c, i) for i, c in enumerate(farkas.coefficients) if c != 0]
        for coef, idx in nonzero:
            constraint = constraints[idx] if idx < len(constraints) else f"C{idx+1}"
            lines.append(f"//   {coef:+.0f} × ({constraint})")
        
        lines.append("// = 0 >= 1  (contradiction)")
        
        return "\n".join(lines)

    def generate_from_quant_inst(self, qi: QuantInstProof,
                                 forall_var: str = "i",
                                 forall_body: str = "P(i)",
                                 bound_expr: str = "n") -> AssertSequence:
        """Generate assertions from quantifier instantiation.

        Args:
            qi: The quantifier instantiation proof
            forall_var: The quantified variable name (extracted from source)
            forall_body: The quantifier body (extracted from source)
            bound_expr: The bound expression (extracted from source, e.g., "|s|")
        """
        # Resolve instantiation values
        values = []
        for v in qi.instantiation_values:
            values.append(self.resolve_name(v))

        assertions = []
        justifications = []

        # Generate assertions based on the instantiation
        if len(values) == 1:
            val = values[0]
            # Show what the instantiation proves
            instantiated_body = forall_body.replace(forall_var, val)
            assertions.append(f"// Instantiate {forall_var} := {val}")
            justifications.append("")
            assertions.append(instantiated_body)
            justifications.append(f"from forall {forall_var} :: ...")
        else:
            # Multiple values - show all
            assertions.append(f"// Instantiate with: {', '.join(values)}")
            justifications.append("")

        return AssertSequence(
            assertions=assertions,
            justifications=justifications
        )

    def generate_from_equality_chain(self, chain: EqualityChain) -> CalcBlock:
        """Generate calc block from equality chain.

        For complex chains with raw Z3 names, we provide a summary.
        """
        steps = []

        # Extract terms from justifications
        resolved_terms = []
        for just in chain.justifications:
            term = self.resolve_name(just)
            resolved_terms.append(term)

        # Check if we have clean terms or raw Z3 internal names
        has_raw_names = any(
            any(marker in term for marker in ['$x', '@x', '?x', 'symm(', 'unit-resolution'])
            for term in resolved_terms
        )

        if has_raw_names:
            # Return empty calc block - summary provided elsewhere
            return CalcBlock(steps=[])

        for i, term in enumerate(resolved_terms):
            steps.append(CalcStep(
                expression=term,
                relation="==",
                justification=f"step {i+1}"
            ))

        return CalcBlock(steps=steps)

    def generate_from_modus_ponens(self, mp: ModusPonens) -> AssertSequence:
        """Generate assertions from modus ponens step.

        For complex internal proofs, we provide a high-level summary rather than
        showing raw Z3 internal names.
        """
        antecedent_str = self.resolve_name(mp.antecedent)
        consequent_str = self.resolve_name(mp.consequent) if mp.consequent else "Q"

        # Check if the strings contain raw Z3 internal names ($x, @x, ?x)
        has_raw_names = any(marker in antecedent_str for marker in ['$x', '@x', '?x', 'asserted(', 'mp(', 'not-or-elim'])

        if has_raw_names:
            # Provide a clean summary instead of raw internal names
            return AssertSequence(
                assertions=["// Proved by modus ponens (Z3 internal reasoning)"],
                justifications=[""]
            )

        return AssertSequence(
            assertions=[
                f"{antecedent_str}",
                f"{antecedent_str} ==> {consequent_str}",
                f"{consequent_str}"
            ],
            justifications=[
                "given",
                "implication",
                "by modus ponens"
            ]
        )

    def generate_from_arithmetic_lemma(self, lemma: ArithmeticLemma) -> str:
        """Generate explanation from arithmetic lemma."""
        lines = []
        lines.append(f"// Arithmetic lemma ({lemma.lemma_type}):")
        
        if lemma.lemma_type == "farkas":
            lines.append(f"// Farkas coefficients: {lemma.coefficients}")
            for i, c in enumerate(lemma.constraints):
                lines.append(f"// C{i+1}: {self.resolve_name(c)}")
        else:
            for i, c in enumerate(lemma.constraints):
                lines.append(f"// {self.resolve_name(c)}")
        
        return "\n".join(lines)

    def generate_transitivity_calc(
            self,
            start: str,
            end: str,
            intermediates: List[str],
            justifications: List[str]
    ) -> CalcBlock:
        """Generate a transitivity calc block."""
        all_terms = [start] + intermediates + [end]
        steps = []

        for i, term in enumerate(all_terms):
            just = justifications[i] if i < len(justifications) else ""
            steps.append(CalcStep(
                expression=term,
                relation="<=",
                justification=just
            ))

        return CalcBlock(steps=steps)

    def generate_implication_calc(
            self,
            premises: List[str],
            conclusions: List[str],
            justifications: List[str]
    ) -> str:
        """Generate a calc block with implications."""
        lines = ["calc ==> {"]
        
        all_steps = list(zip(premises, conclusions))
        for i, (premise, conclusion) in enumerate(all_steps):
            lines.append(f"  {premise};")
            just = justifications[i] if i < len(justifications) else ""
            if just:
                lines.append(f"==> {{ {just} }}")
            else:
                lines.append("==>")
        
        if conclusions:
            lines.append(f"  {conclusions[-1]};")
        
        lines.append("}")
        return "\n".join(lines)


def parse_inequality_constraint(constraint_str: str) -> Optional[tuple]:
    """Parse a constraint string like 'a - b <= 0' into (left_var, op, right_var)."""
    import re

    # Normalize the constraint
    constraint_str = constraint_str.strip()

    # Pattern: var1 - var2 <= 0  means var1 <= var2
    match = re.match(r'^(\w+)\s*-\s*(\w+)\s*<=\s*0$', constraint_str)
    if match:
        return (match.group(1), '<=', match.group(2))

    # Pattern: var1 - var2 >= 0  means var1 >= var2  (or var2 <= var1)
    match = re.match(r'^(\w+)\s*-\s*(\w+)\s*>=\s*0$', constraint_str)
    if match:
        return (match.group(2), '<=', match.group(1))

    # Pattern: var1 <= var2
    match = re.match(r'^(\w+)\s*<=\s*(\w+)$', constraint_str)
    if match:
        return (match.group(1), '<=', match.group(2))

    # Pattern: var1 >= var2
    match = re.match(r'^(\w+)\s*>=\s*(\w+)$', constraint_str)
    if match:
        return (match.group(2), '<=', match.group(1))

    return None


def build_transitivity_chain(constraints: List[str]) -> Optional[List[str]]:
    """Build a transitivity chain from inequality constraints.

    Given constraints like ['a <= b', 'b <= c'], returns ['a', 'b', 'c'].
    """
    # Parse all constraints into (left, op, right) tuples
    parsed = []
    for c in constraints:
        # Skip negated constraints (these are goals, not preconditions)
        if c.startswith('NOT('):
            continue
        p = parse_inequality_constraint(c)
        if p and p[1] == '<=':
            parsed.append((p[0], p[2]))  # (left, right) meaning left <= right

    if not parsed:
        return None

    # Build adjacency: for each var, what comes after it?
    next_var = {}
    prev_var = {}
    all_vars = set()

    for left, right in parsed:
        next_var[left] = right
        prev_var[right] = left
        all_vars.add(left)
        all_vars.add(right)

    # Find the start (variable with no predecessor in the chain)
    start = None
    for v in all_vars:
        if v not in prev_var:
            start = v
            break

    if start is None:
        # Might be a cycle or complex structure
        return None

    # Build the chain
    chain = [start]
    current = start
    while current in next_var:
        current = next_var[current]
        chain.append(current)
        if len(chain) > len(all_vars) + 1:  # Prevent infinite loop
            return None

    return chain if len(chain) > 1 else None


def simplify_constraint(constraint: str) -> str:
    """Simplify a constraint string for display."""
    import re

    # Replace $generated@@N(0) with just 0 (literal wrapper)
    constraint = re.sub(r'\$generated@@\d+\(0\)', '0', constraint)

    # Replace $generated(N) with just N (boxing/unboxing functions)
    constraint = re.sub(r'\$generated\((\d+)\)', r'\1', constraint)

    # Replace LitInt(N) with just N
    constraint = re.sub(r'LitInt\((\d+)\)', r'\1', constraint)

    # Simplify common arithmetic patterns:

    # var - var <= 0  ->  var <= var
    match = re.match(r'^(\w+)\s*-\s*(\w+)\s*<=\s*0$', constraint)
    if match:
        return f"{match.group(1)} <= {match.group(2)}"

    # var - var >= 0  ->  var >= var
    match = re.match(r'^(\w+)\s*-\s*(\w+)\s*>=\s*0$', constraint)
    if match:
        return f"{match.group(1)} >= {match.group(2)}"

    # var - num <= 0  ->  var <= num
    match = re.match(r'^(\w+)\s*-\s*(\d+)\s*<=\s*0$', constraint)
    if match:
        return f"{match.group(1)} <= {match.group(2)}"

    # var - num >= 0  ->  var >= num
    match = re.match(r'^(\w+)\s*-\s*(\d+)\s*>=\s*0$', constraint)
    if match:
        return f"{match.group(1)} >= {match.group(2)}"

    # expr - num == 0  ->  expr == num (for sums like x + y + z - 100 == 0)
    match = re.match(r'^([\w\s\+\-]+)\s*-\s*(\d+)\s*==\s*0$', constraint)
    if match:
        expr = match.group(1).strip()
        # Clean up the expression (remove trailing operators)
        expr = re.sub(r'\s*[\+\-]\s*$', '', expr)
        return f"{expr} == {match.group(2)}"

    # expr <= num or expr >= num (direct comparisons)
    match = re.match(r'^([\w\s\+\-]+)\s*(<=|>=|<|>|==)\s*(\d+)$', constraint)
    if match:
        return f"{match.group(1).strip()} {match.group(2)} {match.group(3)}"

    # Complex expressions with proof operations - try to extract the core
    if 'unit-resolution' in constraint or 'mp(' in constraint or 'rewrite' in constraint:
        # Try to extract a simple inequality from within the complex expression
        # Pattern: var op num where op is <=, >=, <, >, ==
        match = re.search(r'\b(\w+)\s*(<=|>=|<|>|==)\s*(\d+)', constraint)
        if match:
            return f"{match.group(1)} {match.group(2)} {match.group(3)}"
        # Pattern: sum == num
        match = re.search(r'(\w+\s*\+\s*\w+(?:\s*\+\s*\w+)*)\s*==\s*(\d+)', constraint)
        if match:
            return f"{match.group(1)} == {match.group(2)}"
        return "(derived)"

    return constraint


def generate_calc_from_farkas(coefficients: List[float],
                               constraints: List[str],
                               goal: Optional[str] = None) -> str:
    """Generate a Dafny calc block from Farkas proof.

    Args:
        coefficients: Farkas coefficients
        constraints: Resolved constraint strings
        goal: The goal being proved (optional)

    Returns:
        Dafny calc block as string
    """
    lines = []

    # Simplify constraints for readability
    simple_constraints = [simplify_constraint(c) for c in constraints]

    # Try to build a transitivity chain from simple constraints
    chain = build_transitivity_chain(simple_constraints)

    if chain and len(chain) >= 3:
        # Generate transitivity calc block
        lines.append("calc {")
        for i, var in enumerate(chain):
            lines.append(f"  {var};")
            if i < len(chain) - 1:
                # Find the constraint that justifies this step
                left, right = var, chain[i + 1]
                justification = f"{left} <= {right}"
                lines.append(f"<= {{ /* {justification} */ }}")
        lines.append("}")
    else:
        # Extract goal from negated constraint
        goal_expr = None
        goal_var = None
        for c in simple_constraints:
            if c.startswith('NOT('):
                inner = c[4:-1]  # Remove NOT( and )
                goal_expr = inner
                # Try to extract goal variable and bound
                import re
                match = re.match(r'(\w+)\s*-\s*(\d+)\s*<=\s*0', inner)
                if match:
                    goal_var = match.group(1)
                    goal_bound = match.group(2)
                    goal_expr = f"{goal_var} <= {goal_bound}"
                break

        # Generate a calc block showing the bound derivation
        lines.append("calc {")

        # Find preconditions (non-negated, meaningful constraints)
        preconditions = []
        for coef, c in zip(coefficients, simple_constraints):
            if coef != 0 and not c.startswith('NOT(') and c != '(derived)':
                # Filter out tautologies like "100 == 100" or "33 == 33"
                import re
                if re.match(r'^(\d+)\s*==\s*\1$', c):
                    continue
                # Filter out "num == 0" which are likely normalized constraints
                if re.match(r'^\d+\s*==\s*0$', c):
                    continue
                preconditions.append((int(coef), c))

        if goal_var and preconditions:
            # Build a bound proof as assert sequence
            lines.append(f"  // Goal: {goal_expr}")
            lines.append(f"  // From preconditions:")

            for coef, constraint in preconditions:
                lines.append(f"  //   {constraint}")

            lines.append(f"  // Farkas certificate: {[int(c) for c in coefficients if c != 0]}")
            lines.append("}")
            lines.append("")
            lines.append(f"assert {goal_expr};  // proved by Farkas lemma")
        else:
            # Fallback: show the Farkas structure
            lines.append("  // Farkas lemma proof:")
            for coef, constraint in zip(coefficients, simple_constraints):
                if coef != 0:
                    lines.append(f"  //   {coef:+.0f} × ({constraint})")

            if goal_expr:
                lines.append(f"  // Therefore: {goal_expr}")

        lines.append("}")

    return "\n".join(lines)


def generate_dafny_proof(steps: List[ProofStep], mapper: Optional[NameMapper] = None) -> str:
    """Generate Dafny proof from extracted steps.

    We focus on generating useful output for Farkas and quantifier instantiation proofs.
    For other proof types (modus ponens, equality chains), we provide summaries only
    if they contain meaningful information (not raw Z3 internal names).
    """
    generator = DafnyGenerator(mapper)
    output_lines = []

    # Track what types of proofs we have
    has_farkas = False
    has_quant_inst = False
    mp_count = 0
    eq_chain_count = 0

    for step in steps:
        if step.rule == ProofRuleType.FARKAS:
            has_farkas = True
            for arg in step.arguments:
                if isinstance(arg, FarkasProof):
                    output_lines.append(f"// Farkas coefficients: {arg.coefficients}")
                    calc = generator.generate_from_farkas(arg)
                    output_lines.append(calc.to_dafny())
                elif isinstance(arg, ArithmeticLemma):
                    output_lines.append(generator.generate_from_arithmetic_lemma(arg))

        elif step.rule == ProofRuleType.QUANT_INST:
            has_quant_inst = True
            for arg in step.arguments:
                if isinstance(arg, QuantInstProof):
                    values = [str(v) for v in arg.instantiation_values]
                    output_lines.append(f"// Quantifier instantiation with: {', '.join(values)}")
                    asserts = generator.generate_from_quant_inst(arg)
                    output_lines.append(asserts.to_dafny())

        elif step.rule == ProofRuleType.TRANS_STAR:
            eq_chain_count += 1
            for arg in step.arguments:
                if isinstance(arg, EqualityChain):
                    calc = generator.generate_from_equality_chain(arg)
                    # Only include if it has meaningful steps
                    if calc.steps:
                        output_lines.append("// Equality chain:")
                        output_lines.append(calc.to_dafny())

        elif step.rule == ProofRuleType.MP:
            mp_count += 1
            # Only show a few MP steps to avoid clutter
            if mp_count <= 3:
                for arg in step.arguments:
                    if isinstance(arg, ModusPonens):
                        asserts = generator.generate_from_modus_ponens(arg)
                        asserts_str = asserts.to_dafny()
                        # Only include if it has meaningful content
                        if "Z3 internal reasoning" not in asserts_str:
                            output_lines.append("// Modus ponens:")
                            output_lines.append(asserts_str)

        elif step.rule == ProofRuleType.TH_LEMMA_ARITH:
            for arg in step.arguments:
                if isinstance(arg, ArithmeticLemma):
                    output_lines.append(generator.generate_from_arithmetic_lemma(arg))

    # If we had no Farkas proofs and no quant inst, but had MP/chains,
    # provide a summary
    if not has_farkas and not has_quant_inst and (mp_count > 0 or eq_chain_count > 0):
        if not output_lines:
            output_lines.append("// Proof verified by Z3 theory solvers")
            if mp_count > 0:
                output_lines.append(f"// (used {mp_count} modus ponens steps)")
            if eq_chain_count > 0:
                output_lines.append(f"// (used {eq_chain_count} equality chains)")

    return "\n\n".join(output_lines)
