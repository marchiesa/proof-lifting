"""
CEGAR-style proof hint discovery for Dafny/Boogie verification.

When Z3 returns 'unknown', parse the spurious model to find
sequence terms that should be equal but aren't, then inject
Seq#Equal hints and retry.

Uses the name_map JSON from modified Boogie to resolve
$generated@@N names to their Boogie meanings (Seq#Take, etc.)
instead of hardcoding them.

Algorithm:
  1. Load name_map to resolve $generated@@N → Boogie names
  2. Run Z3 on VC → unknown + model
  3. Parse model: extract function tables
  4. For each uninterpreted function f with Seq arguments:
       Find pairs f(_, A) ≠ f(_, B) where A, B are Seq values
       with |A| == |B| in the model
  5. For each such (A, B), recover the original term expressions
     from the Seq#Take table
  6. Inject (assert (Seq#Equal A_term B_term))
  7. Retry Z3
"""

import subprocess
import json
import re
import sys
from collections import defaultdict


def load_name_map(namemap_file: str, vc_number: int | None = None) -> dict:
    """Load the name_map JSON from modified Boogie and build lookup tables.

    Returns a dict with:
      - 'to_boogie': $generated@@N -> Boogie name
      - 'to_smt': Boogie name -> $generated@@N
    """
    with open(namemap_file) as f:
        data = json.load(f)

    # Start with global mappings
    merged = dict(data['variables'])

    # Apply per-VC overrides if vc_number specified
    if vc_number is not None:
        for vc in data.get('perVc', []):
            if vc.get('vc') == vc_number:
                merged.update(vc.get('variables', {}))
                break

    # Build reverse lookup: Boogie name -> $generated@@N
    # For duplicate Boogie names, keep the latest (per-VC override wins)
    to_smt = {}
    for smt_name, boogie_name in merged.items():
        to_smt[boogie_name] = smt_name

    return {'to_boogie': merged, 'to_smt': to_smt}


def resolve_name(name_map: dict, boogie_name: str) -> str | None:
    """Find the $generated@@N name for a Boogie name.

    Supports partial matching: 'Seq#Take' matches 'Seq#Take',
    'segmentSum' matches '_module.__default.segmentSum'.
    """
    to_smt = name_map['to_smt']

    # Exact match first
    if boogie_name in to_smt:
        return to_smt[boogie_name]

    # Partial match: look for Boogie names ending with the query
    for full_name, smt_name in to_smt.items():
        if full_name.endswith('.' + boogie_name) or full_name.endswith(boogie_name):
            return smt_name

    return None


def find_seq_variables(name_map: dict) -> dict:
    """Find all T@Seq-typed variables from the name_map.

    Returns dict of smt_name -> boogie_name for Seq variables.
    Seq variables are identified by their Boogie names (e.g., nums#0).
    """
    # We can't determine types from the name_map alone,
    # so we return all variable mappings and let the caller
    # filter by checking the model.
    return name_map['to_boogie']


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
    seen = set()
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
                            pair = tuple(sorted([seq_a, seq_b]))
                            if pair not in seen:
                                seen.add(pair)
                                candidates.append((seq_a, seq_b, key[0],
                                                   val_a, val_b, len_a))

    return candidates


def build_int_resolver(model: dict, name_map: dict | None,
                       seq_length_func: str) -> dict:
    """Build a map from concrete integer values to symbolic expressions.

    Examines known integer variables (like i#0) and sequence lengths
    to map concrete model values back to symbolic SMT terms.

    Returns dict: concrete_int_str -> symbolic_smt_expr
    """
    resolver = {}
    if not name_map:
        return resolver

    # Find integer variables and their model values
    int_vars = {}  # smt_name -> model_value (as int)
    for smt_name, boogie_name in name_map['to_boogie'].items():
        if smt_name in model and isinstance(model[smt_name], str):
            try:
                val = int(model[smt_name])
                int_vars[smt_name] = val
                resolver[str(val)] = smt_name
            except (ValueError, TypeError):
                pass

    # Find sequence lengths: Seq#Length(seq_var) -> concrete value
    # Collect but don't write to resolver yet — var offsets take priority
    len_exprs = {}  # concrete_value -> symbolic expression
    if seq_length_func in model and isinstance(model[seq_length_func], list):
        for args, result in model[seq_length_func]:
            if len(args) == 1 and args[0].startswith('T@Seq'):
                try:
                    len_val = int(result)
                    for smt_name, boogie_name in name_map['to_boogie'].items():
                        if smt_name in model and model[smt_name] == args[0]:
                            len_expr = f"({seq_length_func} {smt_name})"
                            len_exprs[len_val] = len_expr
                except (ValueError, TypeError):
                    pass

    # Generate offset expressions: var + k takes priority over len + k
    # because VC formulas typically use (+ i 3) not (Seq#Length nums)
    for smt_name, base_val in int_vars.items():
        for offset in range(-10, 11):
            concrete = base_val + offset
            key = str(concrete)
            if key not in resolver:
                if offset == 0:
                    resolver[key] = smt_name
                elif offset > 0:
                    resolver[key] = f"(+ {smt_name} {offset})"
                else:
                    resolver[key] = f"(- {smt_name} {-offset})"

    # Length expressions fill in any remaining gaps
    for len_val, len_expr in len_exprs.items():
        for offset in range(-10, 11):
            concrete = len_val + offset
            key = str(concrete)
            if key not in resolver:
                if offset == 0:
                    resolver[key] = len_expr
                elif offset > 0:
                    resolver[key] = f"(+ {len_expr} {offset})"
                else:
                    resolver[key] = f"(- {len_expr} {-offset})"

    return resolver


def reconstruct_term(seq_val: str, take_origin: dict,
                     var_names: dict,
                     int_resolver: dict | None = None) -> str:
    """Reconstruct the SMT term expression for a Seq value.

    Follows the Seq#Take chain backwards to build the term.
    Uses int_resolver to convert concrete integers to symbolic expressions.
    """
    if seq_val in var_names:
        return var_names[seq_val]
    if seq_val in take_origin:
        func, parent, idx = take_origin[seq_val]
        parent_term = reconstruct_term(parent, take_origin, var_names,
                                       int_resolver)
        # Resolve the index from concrete to symbolic
        if int_resolver and idx in int_resolver:
            idx = int_resolver[idx]
        return f"({func} {parent_term} {idx})"
    return seq_val  # unknown origin


def decompose_take_chain(term: str, seq_take: str) -> list[tuple[str, str]]:
    """Decompose a nested Take chain into step-wise equality hints.

    Given Take(Take(Take(Take(base, n1), n2), n3), n4),
    produces pairwise hints:
      Take(Take(base, n1), n2) == Take(base, n2)
      Take(Take(base, n2), n3) == Take(base, n3)
      Take(Take(base, n3), n4) == Take(base, n4)

    Each hint asserts that taking m elements from Take(s, n) where m < n
    is the same as taking m from the original sequence.
    """
    # Parse the nested Take chain
    # Extract levels: [(parent, index), ...]
    levels = []  # list of (full_term_at_this_level, index)
    current = term
    while current.startswith(f"({seq_take} "):
        # Parse ({seq_take} <inner> <idx>)
        # Remove outer parens and function name
        inner = current[len(f"({seq_take} "):-1]
        # Find where the inner term ends and the index begins
        # Handle nested parens
        depth = 0
        split_pos = 0
        for ci, ch in enumerate(inner):
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
            elif ch == ' ' and depth == 0:
                split_pos = ci
                # Don't break - keep going to find the LAST space at depth 0
        # split_pos is the last space at depth 0
        inner_term = inner[:split_pos]
        idx = inner[split_pos + 1:]
        levels.append((current, inner_term, idx))
        current = inner_term

    base = current  # The innermost non-Take term

    if len(levels) < 2:
        return []  # Nothing to decompose

    # Generate step-wise hints
    # For each consecutive pair of levels, emit:
    #   Take(Take(base, outer_idx), inner_idx) == Take(base, inner_idx)
    # Working from outside in:
    #   levels[0] = outermost Take, levels[-1] = innermost Take
    hints = []
    for i in range(len(levels) - 1):
        _, _, outer_idx = levels[i + 1]  # The index of the enclosing Take
        _, _, inner_idx = levels[i]       # Wait, this isn't right

    # Actually, let's think about this differently.
    # The chain is: Take(Take(Take(Take(base, n1), n2), n3), n4)
    # levels[0] = (full, Take(Take(Take(base, n1), n2), n3), n4)
    # levels[1] = (Take(Take(Take(base, n1), n2), n3), Take(Take(base, n1), n2), n3)
    # levels[2] = (Take(Take(base, n1), n2), Take(base, n1), n2)
    # levels[3] = (Take(base, n1), base, n1)
    # base = base
    #
    # Step-wise hints (from innermost to outermost):
    # Take(Take(base, n1), n2) == Take(base, n2)     [levels[2]]
    # Take(Take(base, n2), n3) == Take(base, n3)      [uses simplified n2]
    # Take(Take(base, n3), n4) == Take(base, n4)      [uses simplified n3]
    #
    # The key insight: Take(Take(s, a), b) == Take(s, b) when b <= a
    # So for each level, we emit:
    #   Seq#Equal(Take(Take(base, levels[k].idx), levels[k-1].idx),
    #             Take(base, levels[k-1].idx))

    seen = set()
    for i in range(len(levels) - 1, 0, -1):
        # levels[i] has index n_outer (the larger index)
        # levels[i-1] has index n_inner (the smaller index)
        n_outer = levels[i][2]
        n_inner = levels[i - 1][2]

        # Hint: Take(Take(base, n_outer), n_inner) == Take(base, n_inner)
        lhs = f"({seq_take} ({seq_take} {base} {n_outer}) {n_inner})"
        rhs = f"({seq_take} {base} {n_inner})"

        key = (lhs, rhs)
        if key not in seen:
            seen.add(key)
            hints.append((lhs, rhs))

    return hints


def main():
    if len(sys.argv) < 2:
        print("Usage: python cegar_prototype.py <smt_file> [--name-map <map.json>] [--vc <N>]")
        print("       python cegar_prototype.py <smt_file>  (legacy mode, hardcoded names)")
        print()
        print("Runs Z3, parses the spurious model, finds Seq equality hints,")
        print("injects them, and retries.")
        print()
        print("Options:")
        print("  --name-map <file>  Name map JSON from modified Boogie (/nameMap flag)")
        print("  --vc <N>           VC number for per-VC name resolution")
        print("  --target <name>    Target function to find hints for (default: segmentSum)")
        print("  --inject           Actually inject hints and re-run Z3")
        sys.exit(1)

    smt_file = sys.argv[1]

    # Parse optional arguments
    namemap_file = None
    vc_number = None
    target_func = 'segmentSum'
    do_inject = False

    i = 2
    while i < len(sys.argv):
        if sys.argv[i] == '--name-map' and i + 1 < len(sys.argv):
            namemap_file = sys.argv[i + 1]
            i += 2
        elif sys.argv[i] == '--vc' and i + 1 < len(sys.argv):
            vc_number = int(sys.argv[i + 1])
            i += 2
        elif sys.argv[i] == '--target' and i + 1 < len(sys.argv):
            target_func = sys.argv[i + 1]
            i += 2
        elif sys.argv[i] == '--inject':
            do_inject = True
            i += 1
        else:
            i += 1

    # Resolve function names
    if namemap_file:
        print(f"Loading name map from {namemap_file}" +
              (f" (VC {vc_number})" if vc_number else ""))
        name_map = load_name_map(namemap_file, vc_number)

        seq_take = resolve_name(name_map, 'Seq#Take')
        seq_length = resolve_name(name_map, 'Seq#Length')
        seq_equal = resolve_name(name_map, 'Seq#Equal')
        segment_sum = resolve_name(name_map, target_func)

        if not seq_take or not seq_length or not seq_equal or not segment_sum:
            print("ERROR: Could not resolve required names from name_map:")
            print(f"  Seq#Take    → {seq_take}")
            print(f"  Seq#Length  → {seq_length}")
            print(f"  Seq#Equal   → {seq_equal}")
            print(f"  {target_func} → {segment_sum}")
            sys.exit(1)

        # Find all Seq-typed variables by checking model later
        # For now, collect candidate variable names from the map
        seq_var_candidates = {}
        for smt_name, boogie_name in name_map['to_boogie'].items():
            # Variables like nums#0, s#0 are sequence variables
            if '#' in boogie_name and not boogie_name.startswith('assert$$') \
               and not boogie_name.startswith('assume$$') \
               and not boogie_name.startswith('aux$$') \
               and 'Fuel' not in boogie_name \
               and 'Frame' not in boogie_name \
               and 'Heap' not in boogie_name \
               and 'alloc' not in boogie_name:
                seq_var_candidates[smt_name] = boogie_name

        print(f"Resolved names:")
        print(f"  Seq#Take   = {seq_take}")
        print(f"  Seq#Length = {seq_length}")
        print(f"  Seq#Equal  = {seq_equal}")
        print(f"  {target_func} = {segment_sum}")
        print(f"  Variable candidates: {seq_var_candidates}")
    else:
        # Legacy hardcoded mode
        print("WARNING: No name map provided, using hardcoded names")
        seq_take = '$generated@@379'
        seq_length = '$generated@@282'
        segment_sum = '$generated@@593'
        seq_equal = '$generated@@601'
        seq_var_candidates = {
            '$generated@@1808': 'nums#0_legacy',
        }

    # Read the SMT file
    with open(smt_file) as f:
        smt_content = f.read()

    # Run Z3 and get model
    modified = smt_content.replace('(check-sat)', '(check-sat)\n(get-model)', 1)
    modified = modified.replace('(get-info :reason-unknown)', '')
    modified = modified.replace('(get-info :rlimit)', '')

    print("\nRunning Z3...")
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

    # Parse the model
    model_text = '\n'.join(lines[1:])
    model = parse_z3_model(model_text)

    # Find candidate equalities
    candidates = find_seq_equalities_to_try(
        model, seq_take, seq_length, [segment_sum])

    if not candidates:
        print("No candidate Seq equalities found in model.")
        return

    print(f"\nFound {len(candidates)} candidate equalities:")
    for seq_a, seq_b, func, val_a, val_b, length in candidates:
        boogie_func = name_map['to_boogie'].get(func, func) if namemap_file else func
        print(f"  {seq_a} vs {seq_b}: {boogie_func}(_, ...)={val_a} vs {val_b}, "
              f"both length={length}")

    # Build take_origin map for term reconstruction
    take_origin = {}
    if isinstance(model.get(seq_take), list):
        for args, result in model[seq_take]:
            if len(args) == 2 and result.startswith('T@Seq'):
                take_origin[result] = (seq_take, args[0], args[1])

    # Map Seq values back to variable names using the name_map
    var_names = {}
    for smt_name, boogie_name in seq_var_candidates.items():
        if smt_name in model and isinstance(model[smt_name], str):
            model_val = model[smt_name]
            if model_val.startswith('T@Seq'):
                var_names[model_val] = smt_name
                print(f"  Variable {smt_name} ({boogie_name}) → {model_val}")

    # Build integer resolver for concrete-to-symbolic translation
    int_resolver = build_int_resolver(
        model, name_map if namemap_file else None, seq_length)
    if int_resolver:
        print(f"\nInteger resolver ({len(int_resolver)} entries):")
        # Show the most relevant entries
        for concrete, symbolic in sorted(int_resolver.items(),
                                         key=lambda x: abs(int(x[0]))
                                         if x[0].lstrip('-').isdigit()
                                         else 9999):
            if not symbolic.startswith('(') and '#' in (
                    name_map['to_boogie'].get(symbolic, '') if namemap_file
                    else ''):
                boogie = name_map['to_boogie'].get(symbolic, symbolic)
                print(f"  {concrete} → {symbolic} ({boogie})")

    # Reconstruct terms and decompose into step-wise hints
    print("\nReconstructed terms:")
    all_step_hints = []
    seen_hints = set()
    for seq_a, seq_b, func, val_a, val_b, length in candidates:
        term_a = reconstruct_term(seq_a, take_origin, var_names, int_resolver)
        term_b = reconstruct_term(seq_b, take_origin, var_names, int_resolver)
        print(f"  {seq_a} = {term_a}")
        print(f"  {seq_b} = {term_b}")

        # Decompose nested Take chains into step-wise hints
        # Try both terms — the deeply nested one will produce steps
        for term in [term_a, term_b]:
            steps = decompose_take_chain(term, seq_take)
            for lhs, rhs in steps:
                key = (lhs, rhs)
                if key not in seen_hints:
                    seen_hints.add(key)
                    all_step_hints.append((lhs, rhs))

    # Display hints
    print(f"\nDecomposed into {len(all_step_hints)} step-wise hints:")
    hints = []
    for lhs, rhs in all_step_hints:
        if namemap_file:
            human_lhs = lhs
            human_rhs = rhs
            for smt_n, boogie_n in name_map['to_boogie'].items():
                human_lhs = human_lhs.replace(smt_n, boogie_n)
                human_rhs = human_rhs.replace(smt_n, boogie_n)
            print(f"  Readable: Seq#Equal({human_lhs}, {human_rhs})")

        hint = f"(assert ({seq_equal} {lhs} {rhs}))"
        hints.append(hint)
        print(f"  SMT:      {hint}")

    # Optionally inject hints and retry
    if do_inject and hints:
        print(f"\n--- Injecting {len(hints)} hints and re-running Z3 ---")
        hint_block = '\n'.join(hints)
        injected = smt_content.replace('(check-sat)',
                                       hint_block + '\n(check-sat)', 1)
        result2 = subprocess.run(['z3', '/dev/stdin'], input=injected,
                                 capture_output=True, text=True, timeout=60)
        output2 = result2.stdout.strip().split('\n')
        print(f"Z3 result with hints: {output2[0]}")


if __name__ == '__main__':
    main()
