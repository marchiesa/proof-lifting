"""
CEGAR-style proof hint discovery for Dafny/Boogie verification.

When Z3 returns 'unknown', parse the spurious model to find
sequence terms that should be equal but aren't, then inject
Seq#Equal hints and retry.

Algorithm:
  1. Run Z3 on VC → unknown + model
  2. Parse model: extract function tables
  3. For each uninterpreted function f with Seq arguments:
       Find pairs f(_, A) ≠ f(_, B) where A, B are Seq values
       with |A| == |B| in the model
  4. For each such (A, B), recover the original term expressions
     from the Seq#Take table
  5. Inject (assert (Seq#Equal A_term B_term))
  6. Retry Z3
"""

import subprocess
import re
import sys
from collections import defaultdict


def parse_z3_model(model_text: str) -> dict:
    """Parse Z3's model output into function tables.

    Returns dict mapping function_name -> list of (args, result) tuples.
    """
    tables = {}
    current_func = None
    current_entries = []

    for line in model_text.split('\n'):
        line = line.strip()

        # Function table header: "funcname -> {"
        m = re.match(r'^(\S+)\s+->\s+\{', line)
        if m:
            if current_func:
                tables[current_func] = current_entries
            current_func = m.group(1)
            current_entries = []
            continue

        # Table entry: "arg1 arg2 -> result"
        if current_func and '->' in line and not line.startswith('}'):
            parts = line.split('->')
            if len(parts) == 2:
                args = parts[0].strip().split()
                result = parts[1].strip()
                current_entries.append((args, result))
            continue

        # End of table
        if line == '}':
            if current_func:
                tables[current_func] = current_entries
                current_func = None
                current_entries = []
            continue

        # Scalar assignment: "name -> value"
        m = re.match(r'^(\S+)\s+->\s+(.+)$', line)
        if m and not current_func:
            tables[m.group(1)] = m.group(2)

    if current_func:
        tables[current_func] = current_entries

    return tables


def find_seq_equalities_to_try(model: dict,
                               seq_take_func: str,
                               seq_length_func: str,
                               target_funcs: list[str]) -> list[tuple]:
    """Find pairs of Seq values that should probably be equal.

    Looks for f(_, A) and f(_, B) where:
    - f is a target function (e.g., segmentSum)
    - A and B are Seq values with the same length
    - f(_, A) ≠ f(_, B) in the model
    """
    # Build length map: Seq value -> length
    length_map = {}
    if seq_length_func in model and isinstance(model[seq_length_func], list):
        for args, result in model[seq_length_func]:
            if len(args) == 1 and args[0].startswith('T@Seq'):
                length_map[args[0]] = result

    # Build reverse Seq#Take map: Seq value -> term expression
    # e.g., T@Seq!val!5 -> Seq#Take(T@Seq!val!2, 8368)
    take_origin = {}
    if seq_take_func in model and isinstance(model[seq_take_func], list):
        for args, result in model[seq_take_func]:
            if len(args) == 2 and result.startswith('T@Seq'):
                take_origin[result] = (seq_take_func, args[0], args[1])

    # For each target function, find Seq argument pairs with same length
    # but different function values
    candidates = []
    for func_name in target_funcs:
        if func_name not in model or not isinstance(model[func_name], list):
            continue

        # Group entries by non-Seq arguments
        # e.g., for segmentSum(layer, seq), group by layer
        by_context = defaultdict(list)
        for args, result in model[func_name]:
            seq_args = [a for a in args if a.startswith('T@Seq')]
            other_args = [a for a in args if not a.startswith('T@Seq')]
            for sa in seq_args:
                key = (func_name, tuple(other_args))
                by_context[key].append((sa, result))

        # Find pairs with same length but different values
        for key, entries in by_context.items():
            for i in range(len(entries)):
                for j in range(i + 1, len(entries)):
                    seq_a, val_a = entries[i]
                    seq_b, val_b = entries[j]
                    if val_a != val_b:
                        len_a = length_map.get(seq_a)
                        len_b = length_map.get(seq_b)
                        if len_a and len_b and len_a == len_b:
                            candidates.append((seq_a, seq_b, key[0],
                                               val_a, val_b, len_a))

    return candidates


def reconstruct_term(seq_val: str, take_origin: dict,
                     var_names: dict) -> str:
    """Reconstruct the SMT term expression for a Seq value.

    Follows the Seq#Take chain backwards to build the term.
    """
    if seq_val in var_names:
        return var_names[seq_val]
    if seq_val in take_origin:
        func, parent, idx = take_origin[seq_val]
        parent_term = reconstruct_term(parent, take_origin, var_names)
        return f"({func} {parent_term} {idx})"
    return seq_val  # unknown origin


def main():
    if len(sys.argv) < 2:
        print("Usage: python cegar_prototype.py <smt_file>")
        print()
        print("Runs Z3, parses the spurious model, finds Seq equality hints,")
        print("injects them, and retries.")
        sys.exit(1)

    smt_file = sys.argv[1]

    # Read the SMT file
    with open(smt_file) as f:
        smt_content = f.read()

    # Run Z3 and get model
    # Add (get-model) after first (check-sat)
    modified = smt_content.replace('(check-sat)', '(check-sat)\n(get-model)', 1)
    modified = modified.replace('(get-info :reason-unknown)', '')
    modified = modified.replace('(get-info :rlimit)', '')

    result = subprocess.run(['z3', '/dev/stdin'], input=modified,
                            capture_output=True, text=True, timeout=60)
    output = result.stdout

    lines = output.strip().split('\n')
    if not lines or lines[0] == 'unsat':
        print("Z3 returned unsat — no hints needed!")
        return

    if lines[0] not in ('unknown', 'sat'):
        print(f"Unexpected Z3 result: {lines[0]}")
        return

    print(f"Z3 returned: {lines[0]}")
    print("Parsing model...")

    # Parse the model (everything after first line)
    model_text = '\n'.join(lines[1:])
    model = parse_z3_model(model_text)

    # We need to know which $generated name is which function.
    # For now, use the names we decoded manually.
    # In a real tool, we'd use the nameMap from modified Boogie.
    seq_take = '$generated@@379'    # Seq#Take
    seq_length = '$generated@@282'  # Seq#Length
    segment_sum = '$generated@@593' # segmentSum
    seq_equal = '$generated@@601'   # Seq#Equal
    nums_var = '$generated@@1808'   # nums
    i_var = '$generated@@1807'      # i

    # Find candidate equalities
    candidates = find_seq_equalities_to_try(
        model, seq_take, seq_length, [segment_sum])

    if not candidates:
        print("No candidate Seq equalities found in model.")
        return

    print(f"\nFound {len(candidates)} candidate equalities:")
    for seq_a, seq_b, func, val_a, val_b, length in candidates:
        print(f"  {seq_a} vs {seq_b}: {func}(_, {seq_a})={val_a}, "
              f"{func}(_, {seq_b})={val_b}, both length={length}")

    # Build take_origin map for term reconstruction
    take_origin = {}
    if isinstance(model.get(seq_take), list):
        for args, result in model[seq_take]:
            if len(args) == 2 and result.startswith('T@Seq'):
                take_origin[result] = (seq_take, args[0], args[1])

    # Map Seq values back to variable names
    var_names = {}
    if nums_var in model:
        var_names[model[nums_var]] = nums_var

    print("\nReconstructed terms:")
    for seq_a, seq_b, func, val_a, val_b, length in candidates:
        term_a = reconstruct_term(seq_a, take_origin, var_names)
        term_b = reconstruct_term(seq_b, take_origin, var_names)
        print(f"  {seq_a} = {term_a}")
        print(f"  {seq_b} = {term_b}")

        hint = f"(assert ({seq_equal} {term_a} {term_b}))"
        print(f"  Hint: {hint}")


if __name__ == '__main__':
    main()
