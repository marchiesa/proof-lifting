"""Find minimal proof chains using Z3's unsat core.

Given a set of axioms and a goal, find the minimal subset of axioms
needed to prove the goal. This gives us the essential proof steps.
"""

import z3
from typing import List, Dict, Tuple, Optional, Set
from dataclasses import dataclass
import re


@dataclass
class LabeledAssertion:
    """An assertion with a label for tracking."""
    label: str
    assertion: z3.ExprRef
    description: str  # Human-readable description
    raw_smt: str = ""  # Original SMT-LIB text


@dataclass
class ProofChain:
    """A minimal proof chain."""
    steps: List[LabeledAssertion]  # Axioms used, in order
    goal: z3.ExprRef


def extract_unsat_core(assertions: List[LabeledAssertion],
                        goal: z3.ExprRef,
                        timeout_ms: int = 30000) -> Optional[List[str]]:
    """Find minimal set of assertions needed to prove the goal.

    Args:
        assertions: Labeled assertions (axioms)
        goal: What we want to prove
        timeout_ms: Timeout in milliseconds

    Returns:
        List of labels for assertions in the unsat core, or None if SAT/timeout
    """
    solver = z3.Solver()
    solver.set('unsat_core', True)
    solver.set('timeout', timeout_ms)

    # Add each assertion with its label as a tracking variable
    for asn in assertions:
        # Create a boolean tracking variable
        tracker = z3.Bool(asn.label)
        # Assert: tracker implies the assertion
        solver.add(z3.Implies(tracker, asn.assertion))

    # Add negation of goal (we want to prove goal, so NOT(goal) should be UNSAT)
    solver.add(z3.Not(goal))

    # Check with all trackers assumed true
    trackers = [z3.Bool(a.label) for a in assertions]
    result = solver.check(*trackers)

    if result == z3.unsat:
        core = solver.unsat_core()
        return [str(c) for c in core]
    elif result == z3.sat:
        print("Goal is not provable with given assertions")
        return None
    else:
        print(f"Z3 returned: {result}")
        return None


def order_proof_steps(core_labels: List[str],
                      assertions: List[LabeledAssertion],
                      goal: z3.ExprRef) -> List[LabeledAssertion]:
    """Order the proof steps by dependency.

    Uses iterative unsat core to find the order:
    - Start with just goal negation
    - Add assertions one at a time
    - The order we need to add them is the proof order
    """
    core_set = set(core_labels)
    core_assertions = [a for a in assertions if a.label in core_set]

    if len(core_assertions) <= 1:
        return core_assertions

    ordered = []
    remaining = list(core_assertions)

    # Try to find an order by checking which assertions are "last needed"
    # This is a heuristic - proper ordering would require deeper analysis

    # For now, just return in original order
    # TODO: Implement proper dependency analysis
    return core_assertions


def find_minimal_proof(smt_content: str,
                       goal_pattern: str,
                       name_map: Dict[str, str] = None) -> Optional[ProofChain]:
    """Find minimal proof from SMT-LIB content.

    Args:
        smt_content: The SMT-LIB file content
        goal_pattern: Pattern to identify the goal assertion
        name_map: Optional mapping from generated names to readable names

    Returns:
        ProofChain with minimal steps, or None
    """
    # Parse SMT-LIB to extract assertions
    assertions = parse_smt_assertions(smt_content, name_map or {})

    # Find the goal
    goal = find_goal(smt_content, goal_pattern)
    if goal is None:
        print(f"Could not find goal matching: {goal_pattern}")
        return None

    # Get unsat core
    core_labels = extract_unsat_core(assertions, goal)
    if core_labels is None:
        return None

    print(f"Unsat core has {len(core_labels)} assertions (out of {len(assertions)})")

    # Order the steps
    ordered_steps = order_proof_steps(core_labels, assertions, goal)

    return ProofChain(steps=ordered_steps, goal=goal)


def parse_smt_assertions(smt_content: str,
                         name_map: Dict[str, str]) -> List[LabeledAssertion]:
    """Parse assertions from SMT-LIB content.

    Extracts (assert ...) forms and labels them.
    """
    assertions = []

    # Find all (assert ...) forms
    # This is a simplified parser - real SMT-LIB can be more complex
    pattern = r'\(assert\s+'

    pos = 0
    idx = 0
    while True:
        match = re.search(pattern, smt_content[pos:])
        if not match:
            break

        start = pos + match.start()

        # Find balanced parentheses
        depth = 0
        end = start
        for i in range(start, len(smt_content)):
            if smt_content[i] == '(':
                depth += 1
            elif smt_content[i] == ')':
                depth -= 1
                if depth == 0:
                    end = i + 1
                    break

        assertion_text = smt_content[start:end]

        # Try to parse with Z3
        try:
            # Create description from the assertion
            desc = create_description(assertion_text, name_map)

            # For now, store as text - we'll parse when needed
            assertions.append(LabeledAssertion(
                label=f"axiom_{idx}",
                assertion=None,  # Will be parsed later
                description=desc,
                raw_smt=assertion_text
            ))
            idx += 1
        except Exception as e:
            pass  # Skip unparseable assertions

        pos = end

    return assertions


def create_description(assertion_text: str, name_map: Dict[str, str]) -> str:
    """Create a human-readable description of an assertion."""
    desc = assertion_text[:100]

    # Apply name mapping
    for gen_name, readable_name in name_map.items():
        desc = desc.replace(gen_name, readable_name)

    # Clean up
    desc = desc.replace('\n', ' ').replace('  ', ' ')

    return desc


def find_goal(smt_content: str, pattern: str) -> Optional[z3.ExprRef]:
    """Find the goal assertion matching the pattern."""
    # TODO: Implement goal finding
    return None


# ============================================================
# Simplified API for common cases
# ============================================================

def prove_equality(lhs: z3.ExprRef,
                   rhs: z3.ExprRef,
                   axioms: List[Tuple[str, z3.ExprRef]],
                   timeout_ms: int = 30000) -> Optional[List[str]]:
    """Prove lhs == rhs using minimal set of axioms.

    Args:
        lhs: Left-hand side expression
        rhs: Right-hand side expression
        axioms: List of (name, axiom) pairs
        timeout_ms: Timeout

    Returns:
        List of axiom names used in proof, or None if unprovable
    """
    assertions = [
        LabeledAssertion(label=name, assertion=axiom, description=name)
        for name, axiom in axioms
    ]

    goal = lhs == rhs

    return extract_unsat_core(assertions, goal, timeout_ms)


# ============================================================
# Test with Sum example
# ============================================================

def test_sum_proof():
    """Test finding minimal proof for Sum(s[..i+1]) == Sum(s[..i]) + s[i]."""

    # Define sorts and functions
    IntSeq = z3.ArraySort(z3.IntSort(), z3.IntSort())

    # Sum function: Seq -> Int
    Sum = z3.Function('Sum', IntSeq, z3.IntSort())

    # Seq operations
    Length = z3.Function('Length', IntSeq, z3.IntSort())
    Take = z3.Function('Take', IntSeq, z3.IntSort(), IntSeq)
    Index = z3.Function('Index', IntSeq, z3.IntSort(), z3.IntSort())

    # Variables
    s = z3.Const('s', IntSeq)
    i = z3.Int('i')

    # Key expressions
    s_take_i = Take(s, i)           # s[..i]
    s_take_i1 = Take(s, i + 1)      # s[..i+1]

    # Axioms - use GROUND INSTANCES instead of ForAll
    axioms = []

    # 1. Sum definition instantiated for s[..i+1]:
    #    Sum(s[..i+1]) == ite(|s[..i+1]|==0, 0, Sum(s[..i+1][..|s[..i+1]|-1]) + s[..i+1][|s[..i+1]|-1])
    sum_unfold_i1 = (
        Sum(s_take_i1) == z3.If(
            Length(s_take_i1) == 0,
            0,
            Sum(Take(s_take_i1, Length(s_take_i1) - 1)) + Index(s_take_i1, Length(s_take_i1) - 1)
        ))
    axioms.append(("sum_unfold_s[..i+1]", sum_unfold_i1))

    # 2. Length(Take(s, i+1)) == i+1 (when valid)
    len_take_i1 = z3.Implies(
        z3.And(0 <= i + 1, i + 1 <= Length(s)),
        Length(s_take_i1) == i + 1
    )
    axioms.append(("|s[..i+1]| == i+1", len_take_i1))

    # 3. Take(Take(s, i+1), i) == Take(s, i)
    #    i.e., s[..i+1][..i] == s[..i]
    take_take_i = z3.Implies(
        z3.And(0 <= i, i <= i + 1),
        Take(s_take_i1, i) == s_take_i
    )
    axioms.append(("s[..i+1][..i] == s[..i]", take_take_i))

    # 4. Index(Take(s, i+1), i) == Index(s, i)
    #    i.e., s[..i+1][i] == s[i]
    idx_take_i = z3.Implies(
        z3.And(0 <= i, i < i + 1),
        Index(s_take_i1, i) == Index(s, i)
    )
    axioms.append(("s[..i+1][i] == s[i]", idx_take_i))

    # 5. Bounds: 0 <= i < Length(s) (loop condition)
    bounds = z3.And(0 <= i, i < Length(s))
    axioms.append(("0 <= i < |s|", bounds))

    # 6. i+1 > 0 (so the else branch of Sum applies)
    i1_pos = (i + 1 > 0)
    axioms.append(("i+1 > 0", i1_pos))

    # Goal: Sum(Take(s, i+1)) == Sum(Take(s, i)) + Index(s, i)
    lhs = Sum(s_take_i1)
    rhs = Sum(s_take_i) + Index(s, i)

    print("Proving: Sum(s[..i+1]) == Sum(s[..i]) + s[i]")
    print(f"With {len(axioms)} axioms:")
    for name, _ in axioms:
        print(f"  - {name}")

    result = prove_equality(lhs, rhs, axioms)

    if result:
        print(f"\nMinimal proof uses {len(result)} axioms:")
        for name in result:
            print(f"  - {name}")
    else:
        print("\nCould not prove")

    return result


def generate_calc_block(axiom_names: List[str]) -> str:
    """Generate a Dafny calc block from the proof steps.

    The order is determined by the logical flow:
    1. Start with goal LHS
    2. Apply axioms in order of dependency
    3. End with goal RHS
    """
    # Normalize axiom names (handle both old and new naming)
    names_set = set(axiom_names)

    lines = []
    lines.append("calc {")
    lines.append("    Sum(s[..i+1]);")

    # Step 1: Unfold Sum definition
    if "sum_unfold_s[..i+1]" in names_set or "sum_unfold_i1" in names_set:
        lines.append("==  // unfold Sum definition")
        lines.append("    Sum(s[..i+1][..|s[..i+1]|-1]) + s[..i+1][|s[..i+1]|-1];")

    # Step 2: Apply |s[..i+1]| == i+1
    if "|s[..i+1]| == i+1" in names_set or "length_take_i1" in names_set:
        lines.append("==  // |s[..i+1]| == i+1")
        lines.append("    Sum(s[..i+1][..i]) + s[..i+1][i];")

    # Step 3: Apply s[..i+1][..i] == s[..i]
    if "s[..i+1][..i] == s[..i]" in names_set or "take_take" in names_set:
        lines.append("==  { assert s[..i+1][..i] == s[..i]; }")
        lines.append("    Sum(s[..i]) + s[..i+1][i];")

    # Step 4: Apply s[..i+1][i] == s[i]
    if "s[..i+1][i] == s[i]" in names_set or "index_take" in names_set:
        lines.append("==  // s[..i+1][i] == s[i]")
        lines.append("    Sum(s[..i]) + s[i];")

    lines.append("}")

    return "\n".join(lines)


def test_sum_proof_with_calc():
    """Test and generate calc block."""
    result = test_sum_proof()

    if result:
        print("\n" + "="*50)
        print("Generated Calc Block:")
        print("="*50)
        print(generate_calc_block(result))


def extract_axioms_from_smt(smt_file: str, name_map: Dict[str, str] = None) -> List[Tuple[str, str]]:
    """Extract axioms from an SMT-LIB file.

    Returns list of (name, smt_text) pairs.
    """
    with open(smt_file, 'r') as f:
        content = f.read()

    axioms = []
    name_map = name_map or {}

    # Find all assert statements
    pattern = r'\(assert\s+'
    pos = 0
    idx = 0

    while True:
        match = re.search(pattern, content[pos:])
        if not match:
            break

        start = pos + match.start()

        # Find balanced parens
        depth = 0
        end = start
        for i in range(start, len(content)):
            if content[i] == '(':
                depth += 1
            elif content[i] == ')':
                depth -= 1
                if depth == 0:
                    end = i + 1
                    break

        assertion = content[start:end]

        # Create readable name
        name = f"axiom_{idx}"

        # Try to identify the axiom type
        if 'forall' in assertion.lower():
            # Look for qid
            qid_match = re.search(r':qid\s+(\S+)', assertion)
            if qid_match:
                name = qid_match.group(1).replace('.', '_')

        axioms.append((name, assertion))
        idx += 1
        pos = end

    return axioms


def find_minimal_proof_from_smt(smt_file: str,
                                 goal_idx: int = -1,
                                 timeout_ms: int = 60000) -> Optional[Tuple[List[int], List[str]]]:
    """Find minimal proof from an SMT file.

    Strategy:
    1. Parse all assertions from the SMT file
    2. The last assertion (or goal_idx) is the goal
    3. Find minimal subset of other assertions needed to prove the goal

    Args:
        smt_file: Path to SMT-LIB file
        goal_idx: Index of the goal assertion (-1 = last)
        timeout_ms: Timeout

    Returns:
        Tuple of (indices of axioms used, list of axiom strings)
    """
    with open(smt_file, 'r') as f:
        content = f.read()

    # Extract declarations and assertions separately
    # We need declarations for context

    # Find all declarations
    decl_pattern = r'\(declare-[^\)]+\)'
    decls = re.findall(decl_pattern, content)

    # Find all assertions with their positions
    assertions = []
    pattern = r'\(assert\s+'
    pos = 0

    while True:
        match = re.search(pattern, content[pos:])
        if not match:
            break

        start = pos + match.start()
        depth = 0
        end = start
        for i in range(start, len(content)):
            if content[i] == '(':
                depth += 1
            elif content[i] == ')':
                depth -= 1
                if depth == 0:
                    end = i + 1
                    break

        assertions.append(content[start:end])
        pos = end

    if not assertions:
        print("No assertions found")
        return None

    print(f"Found {len(decls)} declarations, {len(assertions)} assertions")

    # Separate goal from axioms
    if goal_idx < 0:
        goal_idx = len(assertions) + goal_idx

    goal = assertions[goal_idx]
    axioms = [a for i, a in enumerate(assertions) if i != goal_idx]

    print(f"Goal (assertion {goal_idx}): {goal[:100]}...")
    print(f"Axioms: {len(axioms)}")

    # Build SMT content for checking
    # We'll use check-sat-assuming with named assertions

    solver = z3.Solver()
    solver.set('unsat_core', True)
    solver.set('timeout', timeout_ms)

    # First, parse all declarations to get the context
    decl_str = '\n'.join(decls)

    # Parse each axiom individually and add with tracker
    trackers = []
    parsed_axioms = []

    for i, axiom in enumerate(axioms):
        try:
            # Build a complete SMT string for parsing
            smt_str = decl_str + '\n' + axiom
            parsed = z3.parse_smt2_string(smt_str)

            if parsed:
                tracker = z3.Bool(f'axiom_{i}')
                trackers.append(tracker)
                parsed_axioms.append((i, axiom, parsed[0]))
                solver.add(z3.Implies(tracker, parsed[0]))
        except Exception as e:
            # Skip unparseable axioms
            pass

    print(f"Successfully parsed {len(parsed_axioms)} axioms")

    # Parse and negate the goal
    try:
        smt_str = decl_str + '\n' + goal
        goal_parsed = z3.parse_smt2_string(smt_str)
        if goal_parsed:
            # Negate the goal - we want to prove it by contradiction
            solver.add(z3.Not(goal_parsed[0]))
    except Exception as e:
        print(f"Could not parse goal: {e}")
        return None

    # Check with all axioms enabled
    result = solver.check(*trackers)

    if result == z3.unsat:
        core = solver.unsat_core()
        core_names = [str(c) for c in core]

        # Find the indices
        core_indices = []
        core_axioms = []
        for i, axiom, _ in parsed_axioms:
            if f'axiom_{i}' in core_names:
                core_indices.append(i)
                core_axioms.append(axiom)

        print(f"\nMinimal proof uses {len(core_indices)}/{len(axioms)} axioms")
        return (core_indices, core_axioms)

    elif result == z3.sat:
        print("Goal is NOT provable from the given axioms")
        return None
    else:
        print(f"Z3 returned: {result}")
        return None


@dataclass
class FunctionAxiom:
    """Represents an axiom about a function."""
    name: str
    smt: str
    description: str
    category: str  # "definition", "sequence", "bounds", etc.


def build_function_invariant_query(
    func_name: str,
    func_body: str,  # Dafny function body as string
    invariant_arg: str,  # e.g., "s[..i]"
    next_arg: str,  # e.g., "s[..i+1]"
    index_var: str,  # e.g., "i"
    seq_var: str,  # e.g., "s"
    operation: str = "+",  # The accumulator operation: +, *, etc.
) -> Tuple[str, List[FunctionAxiom]]:
    """Build an SMT query for proving function invariant maintenance.

    Given a recursive function and a loop invariant like:
        invariant result == F(s[..i])

    Build a query to prove:
        F(s[..i+1]) == F(s[..i]) + contribution(i)

    Args:
        func_name: Name of the function (e.g., "Sum")
        func_body: The function definition body
        invariant_arg: The argument in the invariant (e.g., "s[..i]")
        next_arg: The next step argument (e.g., "s[..i+1]")
        index_var: Loop index variable
        seq_var: Sequence variable

    Returns:
        (smt_query, list of FunctionAxiom)
    """
    axioms = []

    # Preamble with sort and function declarations
    preamble = f"""
(set-option :produce-unsat-cores true)
(set-logic ALL)

; Sequence sort
(declare-sort IntSeq 0)
(declare-fun SeqLen (IntSeq) Int)
(declare-fun SeqIdx (IntSeq Int) Int)
(declare-fun SeqTake (IntSeq Int) IntSeq)

; The function we're reasoning about
(declare-fun {func_name} (IntSeq) Int)

; Variables
(declare-const {seq_var} IntSeq)
(declare-const {index_var} Int)
"""

    # Function definition axiom (unfolded for next_arg)
    # For Sum: Sum(s[..i+1]) == ite(|s[..i+1]|==0, 0, Sum(s[..i+1][..-1]) + s[..i+1][-1])
    func_unfold = FunctionAxiom(
        name=f"{func_name.lower()}_unfold",
        smt=f"""
(assert (! (=> (> (SeqLen (SeqTake {seq_var} (+ {index_var} 1))) 0)
              (= ({func_name} (SeqTake {seq_var} (+ {index_var} 1)))
                 ({operation} ({func_name} (SeqTake (SeqTake {seq_var} (+ {index_var} 1)) (- (SeqLen (SeqTake {seq_var} (+ {index_var} 1))) 1)))
                    (SeqIdx (SeqTake {seq_var} (+ {index_var} 1)) (- (SeqLen (SeqTake {seq_var} (+ {index_var} 1))) 1)))))
    :named {func_name.lower()}_unfold))
""",
        description=f"Unfold {func_name} definition for {next_arg}",
        category="definition"
    )
    func_unfold.operation = operation  # Store for calc generation
    axioms.append(func_unfold)

    # Sequence length axiom
    len_axiom = FunctionAxiom(
        name="length_take",
        smt=f"""
(assert (! (=> (and (>= (+ {index_var} 1) 0) (<= (+ {index_var} 1) (SeqLen {seq_var})))
              (= (SeqLen (SeqTake {seq_var} (+ {index_var} 1))) (+ {index_var} 1)))
    :named length_take))
""",
        description=f"|{next_arg}| == {index_var}+1",
        category="sequence"
    )
    axioms.append(len_axiom)

    # Take of Take axiom
    take_take = FunctionAxiom(
        name="take_take",
        smt=f"""
(assert (! (=> (and (>= {index_var} 0) (<= {index_var} (+ {index_var} 1)))
              (= (SeqTake (SeqTake {seq_var} (+ {index_var} 1)) {index_var}) (SeqTake {seq_var} {index_var})))
    :named take_take))
""",
        description=f"{next_arg}[..{index_var}] == {invariant_arg}",
        category="sequence"
    )
    axioms.append(take_take)

    # Index of Take axiom
    index_take = FunctionAxiom(
        name="index_take",
        smt=f"""
(assert (! (=> (and (>= {index_var} 0) (< {index_var} (+ {index_var} 1)))
              (= (SeqIdx (SeqTake {seq_var} (+ {index_var} 1)) {index_var}) (SeqIdx {seq_var} {index_var})))
    :named index_take))
""",
        description=f"{next_arg}[{index_var}] == {seq_var}[{index_var}]",
        category="sequence"
    )
    axioms.append(index_take)

    # Bounds axiom
    bounds = FunctionAxiom(
        name="bounds",
        smt=f"""
(assert (! (and (>= {index_var} 0) (< {index_var} (SeqLen {seq_var})))
    :named bounds))
""",
        description=f"0 <= {index_var} < |{seq_var}|",
        category="bounds"
    )
    axioms.append(bounds)

    # Positive index axiom
    pos = FunctionAxiom(
        name="index_positive",
        smt=f"""
(assert (! (> (+ {index_var} 1) 0)
    :named index_positive))
""",
        description=f"{index_var}+1 > 0",
        category="bounds"
    )
    axioms.append(pos)

    # Goal: NOT(F(next_arg) == F(invariant_arg) op seq[index])
    goal = f"""
(assert (not (= ({func_name} (SeqTake {seq_var} (+ {index_var} 1)))
               ({operation} ({func_name} (SeqTake {seq_var} {index_var})) (SeqIdx {seq_var} {index_var})))))
(check-sat)
(get-unsat-core)
"""

    # Build full query
    smt_query = preamble
    for ax in axioms:
        smt_query += ax.smt
    smt_query += goal

    return smt_query, axioms


def generate_calc_from_axioms(axiom_names: List[str], axioms: List[FunctionAxiom],
                               func_name: str, index_var: str, seq_var: str,
                               operation: str = "+",
                               result_var: str = "result") -> str:
    """Generate a Dafny calc block from the used axioms.

    This is a more general version that uses the axiom metadata.
    """
    names_set = set(axiom_names)

    # Determine the Dafny operator for the given SMT operation
    op_map = {"+": "+", "-": "-", "*": "*", "/": "/", "and": "&&", "or": "||"}
    dafny_op = op_map.get(operation, operation)

    # Infer result variable name from function name
    if func_name.lower() == "sum":
        result_var = "sum"
    elif func_name.lower() == "product":
        result_var = "prod"

    lines = []

    # PRE/POST annotation
    lines.append(f"// ─────────────────────────────────────────────────────────────")
    lines.append(f"// Invariant maintenance for: {result_var} == {func_name}({seq_var}[..{index_var}])")
    lines.append(f"// ─────────────────────────────────────────────────────────────")
    lines.append(f"// PRE:  {result_var} == {func_name}({seq_var}[..{index_var}])  ∧  0 <= {index_var} < |{seq_var}|")
    lines.append(f"// BODY: {result_var} := {result_var} {dafny_op} {seq_var}[{index_var}];  {index_var} := {index_var} + 1;")
    lines.append(f"// POST: {result_var}' == {func_name}({seq_var}[..{index_var}'])   (where {result_var}' and {index_var}' are new values)")
    lines.append(f"//")
    lines.append(f"// Proof: After assignments, {result_var}' = {result_var} {dafny_op} {seq_var}[{index_var}] and {index_var}' = {index_var}+1")
    lines.append(f"//        We need: {result_var}' == {func_name}({seq_var}[..{index_var}'])")
    lines.append(f"//        i.e.:   {result_var} {dafny_op} {seq_var}[{index_var}] == {func_name}({seq_var}[..{index_var}+1])")
    lines.append(f"//        By PRE: {func_name}({seq_var}[..{index_var}]) {dafny_op} {seq_var}[{index_var}] == {func_name}({seq_var}[..{index_var}+1])")
    lines.append(f"// ─────────────────────────────────────────────────────────────")
    lines.append("")

    lines.append("calc {")
    lines.append(f"    {func_name}({seq_var}[..{index_var}+1]);")

    # Find which axioms were used and generate steps
    for ax in axioms:
        if ax.name in names_set:
            if ax.category == "definition":
                lines.append(f"==  // unfold {func_name} definition")
                lines.append(f"    {func_name}({seq_var}[..{index_var}+1][..{index_var}]) {dafny_op} {seq_var}[..{index_var}+1][{index_var}];")
            elif ax.name == "take_take":
                lines.append(f"==  {{ assert {seq_var}[..{index_var}+1][..{index_var}] == {seq_var}[..{index_var}]; }}")
                lines.append(f"    {func_name}({seq_var}[..{index_var}]) {dafny_op} {seq_var}[..{index_var}+1][{index_var}];")
            elif ax.name == "index_take":
                lines.append(f"==  // {ax.description}")
                lines.append(f"    {func_name}({seq_var}[..{index_var}]) {dafny_op} {seq_var}[{index_var}];")

    lines.append("}")

    return "\n".join(lines)


def prove_invariant_maintenance(
    func_name: str,
    seq_var: str = "s",
    index_var: str = "i",
    operation: str = "+",
    func_body: str = ""
) -> Optional[Tuple[List[str], str]]:
    """Prove invariant maintenance for a recursive function.

    Args:
        func_name: Name of the function (e.g., "Sum", "Product", "Max")
        seq_var: Name of the sequence variable
        index_var: Name of the loop index variable
        operation: The accumulator operation ("+", "*", "max", "min")
        func_body: The function body (for pattern detection)

    Returns (list of axiom names used, calc block) or None if unprovable.
    """
    import subprocess
    import tempfile

    # Detect function pattern
    if func_body:
        pattern = detect_function_pattern(func_body)
    else:
        # Infer from operation
        if operation in ("max", "min"):
            pattern = FunctionPattern(
                kind="conditional",
                operation=operation,
                base_case="s[0]",
                recursive_expr=f"if s[i] {'>' if operation == 'max' else '<'} F(s[..i]) then s[i] else F(s[..i])"
            )
        else:
            pattern = FunctionPattern(
                kind="accumulator",
                operation=operation,
                base_case="0" if operation == "+" else "1",
                recursive_expr=f"F(s[..i]) {operation} s[i]"
            )

    # Handle conditional patterns (max, min)
    if pattern.kind == "conditional":
        smt_query, axioms = build_conditional_invariant_query(
            func_name, index_var, seq_var, pattern
        )

        # Write and run Z3
        with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as f:
            f.write(smt_query)
            smt_file = f.name

        result = subprocess.run(['z3', smt_file], capture_output=True, text=True)

        import os
        os.unlink(smt_file)

        if 'unsat' in result.stdout:
            # Parse core
            lines = result.stdout.strip().split('\n')
            core_line = lines[1] if len(lines) > 1 else ""
            core_names = [x.strip() for x in core_line.strip('()').split() if x.strip()]

            # Generate case-split calc block
            calc_block = generate_conditional_calc(func_name, index_var, seq_var, pattern)
            return core_names, calc_block

        return None

    # Handle accumulator patterns (sum, product)
    invariant_arg = f"{seq_var}[..{index_var}]"
    next_arg = f"{seq_var}[..{index_var}+1]"

    smt_query, axioms = build_function_invariant_query(
        func_name, "", invariant_arg, next_arg, index_var, seq_var, operation
    )

    # Write and run Z3
    with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as f:
        f.write(smt_query)
        smt_file = f.name

    result = subprocess.run(['z3', smt_file], capture_output=True, text=True)

    import os
    os.unlink(smt_file)

    if 'unsat' in result.stdout:
        # Parse core
        lines = result.stdout.strip().split('\n')
        core_line = lines[1] if len(lines) > 1 else ""
        core_names = [x.strip() for x in core_line.strip('()').split() if x.strip()]

        # Generate calc block
        calc_block = generate_calc_from_axioms(
            core_names, axioms, func_name, index_var, seq_var, operation
        )

        return core_names, calc_block

    return None


def build_sum_invariant_query(name_map: Dict[str, str]) -> Tuple[str, List[Tuple[str, str]]]:
    """Build an SMT query for Sum invariant maintenance proof.

    Goal: Sum(s[..i+1]) == Sum(s[..i]) + s[i]

    Returns (smt_string, list of (axiom_name, axiom_smt))
    """
    # Use the Z3 Python API to build a cleaner query
    # Then export to SMT-LIB format

    # For now, return a handcrafted SMT query
    axioms = []

    # Declare sorts and functions
    preamble = """
(set-option :produce-unsat-cores true)
(set-logic ALL)

; Sequence sort (use IntSeq to avoid conflict with Z3's built-in Seq)
(declare-sort IntSeq 0)
(declare-fun SeqLen (IntSeq) Int)
(declare-fun SeqIdx (IntSeq Int) Int)
(declare-fun SeqTake (IntSeq Int) IntSeq)

; Sum function
(declare-fun Sum (IntSeq) Int)

; Variables
(declare-const s IntSeq)
(declare-const i Int)
"""

    # Sum definition (ground instance for s[..i+1])
    axioms.append(("sum_unfold_i1", """
(assert (! (=> (> (SeqLen (SeqTake s (+ i 1))) 0)
              (= (Sum (SeqTake s (+ i 1)))
                 (+ (Sum (SeqTake (SeqTake s (+ i 1)) (- (SeqLen (SeqTake s (+ i 1))) 1)))
                    (SeqIdx (SeqTake s (+ i 1)) (- (SeqLen (SeqTake s (+ i 1))) 1)))))
    :named sum_unfold_i1))
"""))

    # Length of Take
    axioms.append(("length_take_i1", """
(assert (! (=> (and (>= (+ i 1) 0) (<= (+ i 1) (SeqLen s)))
              (= (SeqLen (SeqTake s (+ i 1))) (+ i 1)))
    :named length_take_i1))
"""))

    # Take of Take: s[..i+1][..i] == s[..i]
    axioms.append(("take_take", """
(assert (! (=> (and (>= i 0) (<= i (+ i 1)))
              (= (SeqTake (SeqTake s (+ i 1)) i) (SeqTake s i)))
    :named take_take))
"""))

    # Index of Take: s[..i+1][i] == s[i]
    axioms.append(("index_take", """
(assert (! (=> (and (>= i 0) (< i (+ i 1)))
              (= (SeqIdx (SeqTake s (+ i 1)) i) (SeqIdx s i)))
    :named index_take))
"""))

    # Bounds
    axioms.append(("bounds", """
(assert (! (and (>= i 0) (< i (SeqLen s)))
    :named bounds))
"""))

    # i+1 > 0 (for else branch of Sum)
    axioms.append(("i1_positive", """
(assert (! (> (+ i 1) 0)
    :named i1_positive))
"""))

    # Goal: NOT(Sum(s[..i+1]) == Sum(s[..i]) + s[i])
    goal = """
(assert (not (= (Sum (SeqTake s (+ i 1)))
               (+ (Sum (SeqTake s i)) (SeqIdx s i)))))
(check-sat)
(get-unsat-core)
"""

    # Build full query
    smt_query = preamble
    for _, axiom_smt in axioms:
        smt_query += axiom_smt
    smt_query += goal

    return smt_query, axioms


def test_sum_from_smt_query():
    """Test the Sum invariant proof using SMT query directly."""
    import subprocess
    import tempfile

    print("Building SMT query for Sum invariant maintenance...")
    smt_query, axioms = build_sum_invariant_query({})

    # Write to temp file and run Z3
    with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as f:
        f.write(smt_query)
        smt_file = f.name

    print(f"Running Z3 on {smt_file}...")
    result = subprocess.run(['z3', smt_file], capture_output=True, text=True)

    print(f"Z3 output:\n{result.stdout}")
    if result.stderr:
        print(f"Z3 stderr:\n{result.stderr}")

    # Parse unsat core
    if 'unsat' in result.stdout:
        # Extract core names
        core_line = result.stdout.split('\n')[1] if len(result.stdout.split('\n')) > 1 else ""
        print(f"\nUnsat core: {core_line}")

        # Generate calc block
        if core_line:
            core_names = [x.strip() for x in core_line.strip('()').split()]
            print(f"\nMinimal proof uses {len(core_names)} axioms:")
            for name in core_names:
                print(f"  - {name}")
            print("\n" + generate_calc_block(core_names))

    # Cleanup
    import os
    os.unlink(smt_file)


def extract_sum_axioms_from_smt(smt_file: str, name_map: Dict[str, str]) -> List[Tuple[str, str]]:
    """Extract Sum-related axioms from a Boogie-generated SMT file.

    Uses the name map to identify:
    - Sum function definition axiom
    - Sequence operation axioms
    """
    with open(smt_file, 'r') as f:
        content = f.read()

    # Invert name map to find SMT names
    smt_names = {v: k for k, v in name_map.items()}

    sum_func = smt_names.get('_module.__default.Sum', '')
    seq_length = smt_names.get('Seq#Length', '')
    seq_take = smt_names.get('Seq#Take', '')
    seq_index = smt_names.get('Seq#Index', '')

    print(f"Looking for functions:")
    print(f"  Sum: {sum_func}")
    print(f"  Seq#Length: {seq_length}")
    print(f"  Seq#Take: {seq_take}")
    print(f"  Seq#Index: {seq_index}")

    # Find assertions containing these functions
    axioms = []
    pattern = r'\(assert\s+'
    pos = 0
    idx = 0

    while True:
        match = re.search(pattern, content[pos:])
        if not match:
            break

        start = pos + match.start()
        depth = 0
        end = start
        for j in range(start, len(content)):
            if content[j] == '(':
                depth += 1
            elif content[j] == ')':
                depth -= 1
                if depth == 0:
                    end = j + 1
                    break

        assertion = content[start:end]

        # Check if this assertion involves Sum or sequence operations
        is_relevant = False
        if sum_func and sum_func in assertion:
            is_relevant = True
        if seq_length and seq_length in assertion and 'forall' in assertion:
            is_relevant = True
        if seq_take and seq_take in assertion and 'forall' in assertion:
            is_relevant = True

        if is_relevant:
            # Try to identify the axiom type
            name = f"axiom_{idx}"
            if sum_func in assertion and 'ite' in assertion:
                name = "sum_definition"
            elif seq_length in assertion and seq_take in assertion:
                name = "length_take"
            elif seq_take in assertion and 'forall' in assertion:
                name = "take_axiom"

            axioms.append((name, assertion))

        idx += 1
        pos = end

    return axioms


def generate_loop_invariant_calc(
    func_name: str,
    func_body_type: str,  # "sum" for +, "product" for *, "max", "min"
    seq_var: str = "s",
    index_var: str = "i",
    func_body: str = "",
    verbose: bool = False
) -> Optional[str]:
    """Generate a calc block for loop invariant maintenance.

    This is the main API for integration with extract_proof.py.

    Args:
        func_name: Name of the recursive function
        func_body_type: Type of accumulator ("sum" -> +, "product" -> *, "max", "min")
        seq_var: Name of the sequence variable
        index_var: Name of the loop index variable
        func_body: The actual function body (for pattern detection)
        verbose: Print debug info

    Returns:
        Dafny calc block string, or None if unprovable
    """
    # Map body type to operation
    op_map = {"sum": "+", "product": "*", "max": "max", "min": "min"}
    operation = op_map.get(func_body_type.lower(), "+")

    if verbose:
        print(f"Generating calc block for {func_name}({seq_var}[..{index_var}])")
        print(f"  Operation: {operation}")

    result = prove_invariant_maintenance(func_name, seq_var, index_var, operation, func_body)

    if result:
        core_names, calc_block = result
        if verbose:
            print(f"  Minimal proof uses {len(core_names)} axioms")
        return calc_block

    return None


@dataclass
class FunctionPattern:
    """Describes the pattern of a recursive function."""
    kind: str  # "accumulator" or "conditional"
    operation: str  # "+", "*", "max", "min", etc.
    base_case: str  # "0", "1", "s[0]", etc.
    recursive_expr: str  # How recursion is combined


def analyze_function_body(func_body: str) -> str:
    """Analyze a Dafny function body to determine its accumulator type.

    Args:
        func_body: The function body as a string

    Returns:
        Type string: "sum", "product", "max", "min", or "unknown"
    """
    # Simple heuristic based on operators in the body
    if " + " in func_body:
        return "sum"
    elif " * " in func_body:
        return "product"
    elif "max(" in func_body.lower() or "> " in func_body:
        return "max"
    elif "min(" in func_body.lower() or "< " in func_body:
        return "min"
    else:
        return "sum"  # Default to sum


def detect_function_pattern(func_body: str) -> FunctionPattern:
    """Detect the pattern of a recursive function body.

    Args:
        func_body: The function body as a string (Dafny expression)

    Returns:
        FunctionPattern describing the structure
    """
    body_lower = func_body.lower()

    # Check for conditional pattern: if cond then a else b
    if " if " in body_lower and " then " in body_lower and " else " in body_lower:
        # Check if it's a max/min pattern
        if " > " in func_body or " >= " in func_body:
            return FunctionPattern(
                kind="conditional",
                operation="max",
                base_case="s[0]",
                recursive_expr="if s[i] > F(s[..i]) then s[i] else F(s[..i])"
            )
        elif " < " in func_body or " <= " in func_body:
            return FunctionPattern(
                kind="conditional",
                operation="min",
                base_case="s[0]",
                recursive_expr="if s[i] < F(s[..i]) then s[i] else F(s[..i])"
            )

    # Check for accumulator pattern
    if " + " in func_body:
        return FunctionPattern(
            kind="accumulator",
            operation="+",
            base_case="0",
            recursive_expr="F(s[..i]) + s[i]"
        )
    elif " * " in func_body:
        return FunctionPattern(
            kind="accumulator",
            operation="*",
            base_case="1",
            recursive_expr="F(s[..i]) * s[i]"
        )

    # Default to sum
    return FunctionPattern(
        kind="accumulator",
        operation="+",
        base_case="0",
        recursive_expr="F(s[..i]) + s[i]"
    )


def build_conditional_invariant_query(
    func_name: str,
    index_var: str,
    seq_var: str,
    pattern: FunctionPattern,
) -> Tuple[str, List[FunctionAxiom]]:
    """Build SMT query for conditional functions like Max/Min.

    For Max: Max(s[..i+1]) == if s[i] > Max(s[..i]) then s[i] else Max(s[..i])
    """
    axioms = []

    preamble = f"""
(set-option :produce-unsat-cores true)
(set-logic ALL)

; Sequence sort
(declare-sort IntSeq 0)
(declare-fun SeqLen (IntSeq) Int)
(declare-fun SeqIdx (IntSeq Int) Int)
(declare-fun SeqTake (IntSeq Int) IntSeq)

; The function
(declare-fun {func_name} (IntSeq) Int)

; Variables
(declare-const {seq_var} IntSeq)
(declare-const {index_var} Int)
"""

    # Conditional function axiom
    if pattern.operation == "max":
        func_axiom = FunctionAxiom(
            name=f"{func_name.lower()}_unfold",
            smt=f"""
(assert (! (=> (> (SeqLen (SeqTake {seq_var} (+ {index_var} 1))) 0)
              (= ({func_name} (SeqTake {seq_var} (+ {index_var} 1)))
                 (ite (> (SeqIdx {seq_var} {index_var}) ({func_name} (SeqTake {seq_var} {index_var})))
                      (SeqIdx {seq_var} {index_var})
                      ({func_name} (SeqTake {seq_var} {index_var})))))
    :named {func_name.lower()}_unfold))
""",
            description=f"{func_name}(s[..i+1]) == if s[i] > {func_name}(s[..i]) then s[i] else {func_name}(s[..i])",
            category="definition"
        )
    else:  # min
        func_axiom = FunctionAxiom(
            name=f"{func_name.lower()}_unfold",
            smt=f"""
(assert (! (=> (> (SeqLen (SeqTake {seq_var} (+ {index_var} 1))) 0)
              (= ({func_name} (SeqTake {seq_var} (+ {index_var} 1)))
                 (ite (< (SeqIdx {seq_var} {index_var}) ({func_name} (SeqTake {seq_var} {index_var})))
                      (SeqIdx {seq_var} {index_var})
                      ({func_name} (SeqTake {seq_var} {index_var})))))
    :named {func_name.lower()}_unfold))
""",
            description=f"{func_name}(s[..i+1]) == if s[i] < {func_name}(s[..i]) then s[i] else {func_name}(s[..i])",
            category="definition"
        )
    axioms.append(func_axiom)

    # Bounds
    bounds = FunctionAxiom(
        name="bounds",
        smt=f"""
(assert (! (and (>= {index_var} 0) (< {index_var} (SeqLen {seq_var})))
    :named bounds))
""",
        description=f"0 <= {index_var} < |{seq_var}|",
        category="bounds"
    )
    axioms.append(bounds)

    # Positive index
    pos = FunctionAxiom(
        name="index_positive",
        smt=f"""
(assert (! (> (+ {index_var} 1) 0)
    :named index_positive))
""",
        description=f"{index_var}+1 > 0",
        category="bounds"
    )
    axioms.append(pos)

    # Length of Take axiom
    len_take = FunctionAxiom(
        name="length_take",
        smt=f"""
(assert (! (=> (and (>= (+ {index_var} 1) 0) (<= (+ {index_var} 1) (SeqLen {seq_var})))
              (= (SeqLen (SeqTake {seq_var} (+ {index_var} 1))) (+ {index_var} 1)))
    :named length_take))
""",
        description=f"|{seq_var}[..{index_var}+1]| == {index_var}+1",
        category="sequence"
    )
    axioms.append(len_take)

    # Length positive implies content
    len_pos = FunctionAxiom(
        name="length_positive",
        smt=f"""
(assert (! (> (SeqLen (SeqTake {seq_var} (+ {index_var} 1))) 0)
    :named length_positive))
""",
        description=f"|{seq_var}[..{index_var}+1]| > 0",
        category="sequence"
    )
    axioms.append(len_pos)

    # For conditional, we prove two cases separately
    # Case 1: s[i] > F(s[..i]) => F(s[..i+1]) == s[i]
    # Case 2: s[i] <= F(s[..i]) => F(s[..i+1]) == F(s[..i])

    # Goal: The function definition implies the result
    # We check that the ite is well-defined
    if pattern.operation == "max":
        goal = f"""
(assert (not (= ({func_name} (SeqTake {seq_var} (+ {index_var} 1)))
               (ite (> (SeqIdx {seq_var} {index_var}) ({func_name} (SeqTake {seq_var} {index_var})))
                    (SeqIdx {seq_var} {index_var})
                    ({func_name} (SeqTake {seq_var} {index_var}))))))
(check-sat)
(get-unsat-core)
"""
    else:
        goal = f"""
(assert (not (= ({func_name} (SeqTake {seq_var} (+ {index_var} 1)))
               (ite (< (SeqIdx {seq_var} {index_var}) ({func_name} (SeqTake {seq_var} {index_var})))
                    (SeqIdx {seq_var} {index_var})
                    ({func_name} (SeqTake {seq_var} {index_var}))))))
(check-sat)
(get-unsat-core)
"""

    smt_query = preamble
    for ax in axioms:
        smt_query += ax.smt
    smt_query += goal

    return smt_query, axioms


def generate_conditional_calc(
    func_name: str,
    index_var: str,
    seq_var: str,
    pattern: FunctionPattern,
    result_var: str = "m",  # The variable tracking the result
) -> str:
    """Generate a case-split calc block for conditional functions."""

    if pattern.operation == "max":
        cmp = ">"
        cmp_word = "greater"
    else:
        cmp = "<"
        cmp_word = "less"

    # PRE/POST annotation showing the invariant maintenance proof
    return f"""// ─────────────────────────────────────────────────────────────
// Invariant maintenance for: {result_var} == {func_name}({seq_var}[..{index_var}])
// ─────────────────────────────────────────────────────────────
// PRE:  {result_var} == {func_name}({seq_var}[..{index_var}])  ∧  0 <= {index_var} < |{seq_var}|
// BODY: if {seq_var}[{index_var}] {cmp} {result_var} {{ {result_var} := {seq_var}[{index_var}]; }}  {index_var} := {index_var} + 1;
// POST: {result_var}' == {func_name}({seq_var}[..{index_var}'])   (where {result_var}' and {index_var}' are new values)
//
// Proof: After assignments, {index_var}' = {index_var}+1, so we need {result_var}' == {func_name}({seq_var}[..{index_var}+1])
//        By {func_name} definition: {func_name}({seq_var}[..{index_var}+1]) =
//          if {seq_var}[{index_var}] {cmp} {func_name}({seq_var}[..{index_var}]) then {seq_var}[{index_var}] else {func_name}({seq_var}[..{index_var}])
//        Since {result_var} == {func_name}({seq_var}[..{index_var}]) (PRE), this matches the code's if-then-else.
// ─────────────────────────────────────────────────────────────

// Helper assertions for {func_name} unfolding
assert |{seq_var}[..{index_var}+1]| == {index_var} + 1;
assert {seq_var}[..{index_var}+1][..{index_var}] == {seq_var}[..{index_var}];
assert {seq_var}[..{index_var}+1][{index_var}] == {seq_var}[{index_var}];

// Case analysis: {seq_var}[{index_var}] {cmp} {func_name}({seq_var}[..{index_var}])?
if {seq_var}[{index_var}] {cmp} {func_name}({seq_var}[..{index_var}]) {{
    // Case: {seq_var}[{index_var}] is {cmp_word}, so {func_name}({seq_var}[..{index_var}+1]) == {seq_var}[{index_var}]
    calc {{
        {func_name}({seq_var}[..{index_var}+1]);
    ==  {{ assert {seq_var}[..{index_var}+1][|{seq_var}[..{index_var}+1]|-1] == {seq_var}[{index_var}];
           assert {func_name}({seq_var}[..{index_var}+1][..|{seq_var}[..{index_var}+1]|-1]) == {func_name}({seq_var}[..{index_var}]); }}
        {seq_var}[{index_var}];
    }}
}} else {{
    // Case: {seq_var}[{index_var}] is not {cmp_word}, so {func_name}({seq_var}[..{index_var}+1]) == {func_name}({seq_var}[..{index_var}])
    calc {{
        {func_name}({seq_var}[..{index_var}+1]);
    ==  {{ assert {seq_var}[..{index_var}+1][|{seq_var}[..{index_var}+1]|-1] == {seq_var}[{index_var}];
           assert {func_name}({seq_var}[..{index_var}+1][..|{seq_var}[..{index_var}+1]|-1]) == {func_name}({seq_var}[..{index_var}]); }}
        {func_name}({seq_var}[..{index_var}]);
    }}
}}"""


def test_general_approach():
    """Test the general invariant proof approach."""
    print("Testing general invariant proof approach...")
    print("=" * 60)

    result = prove_invariant_maintenance("Sum", "s", "i")

    if result:
        core_names, calc_block = result
        print(f"\nMinimal proof uses {len(core_names)} axioms:")
        for name in core_names:
            print(f"  - {name}")
        print("\nGenerated calc block:")
        print(calc_block)
    else:
        print("Could not prove invariant maintenance")


if __name__ == "__main__":
    import sys

    if len(sys.argv) > 1:
        if sys.argv[1] == "--smt-query":
            # Test with SMT query
            test_sum_from_smt_query()
        elif sys.argv[1] == "--general":
            # Test general approach
            test_general_approach()
        elif sys.argv[1] == "--prove":
            # Prove invariant maintenance for a function
            # Usage: --prove FuncName seqVar indexVar [operation]
            func_name = sys.argv[2] if len(sys.argv) > 2 else "Sum"
            seq_var = sys.argv[3] if len(sys.argv) > 3 else "s"
            index_var = sys.argv[4] if len(sys.argv) > 4 else "i"
            operation = sys.argv[5] if len(sys.argv) > 5 else "+"

            print(f"Proving invariant maintenance for {func_name}({seq_var}[..{index_var}])...")
            print(f"Operation: {operation}")
            result = prove_invariant_maintenance(func_name, seq_var, index_var, operation)

            if result:
                core_names, calc_block = result
                print(f"\nMinimal proof uses {len(core_names)} axioms:")
                for name in core_names:
                    print(f"  - {name}")
                print("\nGenerated calc block:")
                print(calc_block)
            else:
                print("Could not prove invariant maintenance")
        else:
            # Use SMT file from command line
            smt_file = sys.argv[1]
            goal_idx = int(sys.argv[2]) if len(sys.argv) > 2 else -1
            result = find_minimal_proof_from_smt(smt_file, goal_idx)
            if result:
                indices, axiom_strs = result
                print(f"\nMinimal proof uses {len(indices)} axioms")
                for i, ax in zip(indices, axiom_strs):
                    print(f"  [{i}]: {ax[:100]}...")
    else:
        # Run hand-written test
        test_sum_proof_with_calc()
