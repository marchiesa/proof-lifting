#!/usr/bin/env python3
"""
Check that solution files haven't modified the formal spec or code logic.

Approach: extract brace-matched blocks, find them by name, compare.
"""

import re
import sys
import os


def find_blocks(text):
    """
    Parse Dafny text into top-level blocks.
    Returns list of (kind, name, full_text, body_text) where:
    - kind: 'predicate', 'function', 'method', 'lemma', 'ghost_predicate', etc.
    - name: the identifier name
    - full_text: complete text of the block
    - body_text: text inside the outermost braces
    """
    blocks = []
    lines = text.split('\n')
    i = 0

    while i < len(lines):
        line = lines[i].strip()

        # Detect block-starting keywords
        kind = None
        m = None
        for kw in ['ghost predicate', 'ghost function', 'predicate', 'function', 'lemma', 'method']:
            pattern = rf'^{kw}\s+(?:\{{[^}}]*\}}\s+)?(\w+)'
            m = re.match(pattern, line)
            if m:
                kind = kw.replace(' ', '_')
                break

        if not kind or not m:
            i += 1
            continue

        name = m.group(1)
        block_start = i

        # Scan backwards for attributes/comments attached to this block
        # (we keep the block from its first line)

        # Find matching closing brace
        brace_depth = 0
        found_open = False
        j = i
        body_start = -1
        body_end = -1

        while j < len(lines):
            for ci, ch in enumerate(lines[j]):
                if ch == '{':
                    if not found_open:
                        found_open = True
                        body_start = j
                    brace_depth += 1
                elif ch == '}':
                    brace_depth -= 1
                    if found_open and brace_depth == 0:
                        body_end = j
                        break
            if body_end >= 0:
                break
            j += 1

        if body_end < 0:
            i += 1
            continue

        full_text = '\n'.join(lines[block_start:body_end + 1])
        body_text = '\n'.join(lines[body_start:body_end + 1])

        # Extract signature: everything from block_start to body_start (inclusive of opening brace line)
        sig_text = '\n'.join(lines[block_start:body_start + 1])

        blocks.append({
            'kind': kind,
            'name': name,
            'full_text': full_text,
            'body_text': body_text,
            'sig_text': sig_text,
            'start': block_start,
            'end': body_end,
        })

        i = body_end + 1

    return blocks


def extract_method_code_lines(body_text):
    """
    From a method body (including outer braces), extract only the
    "real code" lines — stripping invariants, asserts, ghost vars,
    decreases, lemma calls, forall proof blocks, and ghost assignments.

    Returns list of normalized (stripped) lines.
    """
    lines = body_text.split('\n')

    # First pass: identify ghost variable names
    ghost_vars = set()
    for line in lines:
        m = re.match(r'\s*ghost\s+var\s+(\w+)', line.strip())
        if m:
            ghost_vars.add(m.group(1))

    # Second pass: identify proof-only forall blocks and skip them
    # A forall block looks like: forall ... ensures ... { ... }
    # We need to skip these entirely (they're proof steps, not code)

    result = []
    skip_depth = 0  # when > 0, we're inside a block to skip
    brace_depth = 0
    in_forall_block = False

    for idx, line in enumerate(lines):
        stripped = line.strip()

        # Track brace depth for forall/assert-by skipping
        if skip_depth > 0:
            for ch in line:
                if ch == '{':
                    skip_depth += 1
                elif ch == '}':
                    skip_depth -= 1
            continue

        # Check if this starts a forall proof block
        if re.match(r'\s*forall\b', stripped):
            # Count braces to skip the whole block
            skip_depth = 0
            for ch in line:
                if ch == '{':
                    skip_depth += 1
                elif ch == '}':
                    skip_depth -= 1
            if skip_depth > 0 or '{' not in line:
                # Multi-line forall — the brace might be on a later line
                # We need to find and skip it
                if '{' not in line:
                    # Look ahead for the opening brace
                    skip_depth = -1  # sentinel: skip until we find opening brace
                continue
            continue

        if skip_depth == -1:
            # We're looking for the opening brace of a forall
            if '{' in line:
                skip_depth = 0
                for ch in line:
                    if ch == '{':
                        skip_depth += 1
                    elif ch == '}':
                        skip_depth -= 1
            continue

        # Skip verification-only lines
        should_skip = False

        # invariant
        if re.match(r'\s*invariant\b', stripped):
            should_skip = True

        # assert (including multi-line assert ... by { ... })
        if re.match(r'\s*assert\b', stripped):
            # Check if it spans multiple lines (assert ... by { ... })
            if '{' in stripped:
                skip_depth = 0
                for ch in line:
                    if ch == '{':
                        skip_depth += 1
                    elif ch == '}':
                        skip_depth -= 1
            should_skip = True

        # assume
        if re.match(r'\s*assume\b', stripped):
            should_skip = True

        # ghost var
        if re.match(r'\s*ghost\s+var\b', stripped):
            should_skip = True

        # decreases (inside while loops — not at method level)
        if re.match(r'\s*decreases\b', stripped):
            should_skip = True

        # Ghost variable assignments
        if ghost_vars:
            for gv in ghost_vars:
                if re.match(rf'\s*{re.escape(gv)}\s*:=', stripped):
                    should_skip = True
                    break

        # Bare lemma/function calls (not assignments, not control flow)
        # Pattern: identifier( ... ); at statement level
        if (re.match(r'\s*[a-zA-Z]\w*\s*\(', stripped) and
            not re.match(r'\s*(if|while|return|var|print|assert|assume|expect)\b', stripped) and
            not re.match(r'\s*\w+\s*:=', stripped) and
            stripped.endswith(';')):
            should_skip = True

        # Blank lines and comments
        if stripped == '' or stripped.startswith('//'):
            should_skip = True

        if not should_skip:
            result.append(stripped)

    return result


def normalize_spec_block(text):
    """Normalize a spec block for comparison: strip trailing whitespace per line, normalize spaces."""
    lines = text.split('\n')
    result = []
    for line in lines:
        # Normalize: strip trailing ws, collapse multiple spaces, strip trailing &/&&
        l = line.rstrip()
        # Remove trailing // comments
        # Don't remove comments inside the spec body though — only trailing ones
        result.append(l)
    return '\n'.join(result)


def normalize_for_comparison(text):
    """Aggressively normalize for comparison: strip all whitespace differences."""
    # Remove all comments
    text = re.sub(r'//[^\n]*', '', text)
    # Remove blank lines
    lines = [l.strip() for l in text.split('\n') if l.strip()]
    # Normalize whitespace within lines
    lines = [re.sub(r'\s+', ' ', l) for l in lines]
    return '\n'.join(lines)


def extract_sig_lines(sig_text):
    """Extract method signature lines (method decl + requires + ensures), normalized."""
    lines = sig_text.split('\n')
    result = []
    for line in lines:
        stripped = line.strip()
        if stripped and not stripped.startswith('//'):
            # Remove trailing comments
            stripped = re.sub(r'\s*//.*$', '', stripped).strip()
            if stripped:
                # Normalize whitespace
                result.append(re.sub(r'\s+', ' ', stripped))
    return result


def compare_problem(orig_path, sol_path):
    """Compare original and solution. Return list of issues."""
    with open(orig_path) as f:
        orig_text = f.read()
    with open(sol_path) as f:
        sol_text = f.read()

    orig_blocks = find_blocks(orig_text)
    sol_blocks = find_blocks(sol_text)

    issues = []

    # Find the main method in original
    orig_methods = [b for b in orig_blocks if b['kind'] == 'method']
    if not orig_methods:
        issues.append("No method found in original!")
        return issues
    orig_method = orig_methods[0]
    method_name = orig_method['name']

    # Find spec blocks in original (everything that's not the method)
    orig_specs = [b for b in orig_blocks if b['kind'] != 'method']

    # === CHECK 1: Spec predicates/functions unchanged ===
    for orig_spec in orig_specs:
        sol_match = [b for b in sol_blocks if b['name'] == orig_spec['name'] and
                     b['kind'] == orig_spec['kind']]
        if not sol_match:
            # Try without kind match (ghost predicate vs predicate)
            sol_match = [b for b in sol_blocks if b['name'] == orig_spec['name']]

        if not sol_match:
            issues.append(f"SPEC MISSING: {orig_spec['kind']} {orig_spec['name']} not found in solution")
            continue

        orig_norm = normalize_for_comparison(orig_spec['full_text'])
        sol_norm = normalize_for_comparison(sol_match[0]['full_text'])

        if orig_norm != sol_norm:
            issues.append(f"SPEC CHANGED: {orig_spec['kind']} {orig_spec['name']}")
            # Show first difference
            orig_lines = orig_norm.split('\n')
            sol_lines = sol_norm.split('\n')
            for i in range(max(len(orig_lines), len(sol_lines))):
                ol = orig_lines[i] if i < len(orig_lines) else '<missing>'
                sl = sol_lines[i] if i < len(sol_lines) else '<missing>'
                if ol != sl:
                    issues.append(f"  ORIG: {ol}")
                    issues.append(f"  SOL:  {sl}")
                    break

    # === CHECK 2: Method signature unchanged ===
    sol_method_matches = [b for b in sol_blocks if b['kind'] == 'method' and b['name'] == method_name]
    if not sol_method_matches:
        issues.append(f"MAIN METHOD '{method_name}' not found in solution!")
        return issues

    sol_method = sol_method_matches[0]

    orig_sig = extract_sig_lines(orig_method['sig_text'])
    sol_sig = extract_sig_lines(sol_method['sig_text'])

    if orig_sig != sol_sig:
        issues.append(f"METHOD SIGNATURE CHANGED for '{method_name}':")
        for l in orig_sig:
            issues.append(f"  ORIG: {l}")
        issues.append("  ---")
        for l in sol_sig:
            issues.append(f"  SOL:  {l}")

    # === CHECK 3: Code logic unchanged ===
    orig_code = extract_method_code_lines(orig_method['body_text'])
    sol_code = extract_method_code_lines(sol_method['body_text'])

    if orig_code != sol_code:
        issues.append(f"CODE LOGIC CHANGED in '{method_name}':")
        # Aligned diff
        import difflib
        diff = list(difflib.unified_diff(orig_code, sol_code, lineterm='',
                                          fromfile='original', tofile='solution'))
        for d in diff[:30]:
            issues.append(f"  {d}")

    return issues


def main():
    problems = [0, 2, 4, 15, 27, 33, 34, 40, 52, 57]
    base_dir = os.path.dirname(os.path.abspath(__file__))
    leetcode_dir = os.path.join(os.path.dirname(base_dir), 'LeetcodeDafny', 'leetcode_tests')

    all_pass = True

    for pid in problems:
        orig_path = os.path.join(leetcode_dir, str(pid), 'code-dafny-with-spec.dfy')
        for approach in ['A', 'B']:
            sol_path = os.path.join(base_dir, f'p{pid}_approach{approach}.dfy')

            if not os.path.exists(sol_path):
                print(f"P{pid} Approach {approach}: SKIP (file not found)")
                continue

            issues = compare_problem(orig_path, sol_path)

            if issues:
                print(f"P{pid} Approach {approach}: FAIL")
                for issue in issues:
                    print(f"  {issue}")
                all_pass = False
            else:
                print(f"P{pid} Approach {approach}: PASS")

    print()
    if all_pass:
        print("ALL CHECKS PASSED")
    else:
        print("SOME CHECKS FAILED - review above")

    return 0 if all_pass else 1


if __name__ == '__main__':
    sys.exit(main())
