#!/usr/bin/env python3
"""Check that an LLM-generated Verus program preserves the formal spec and exec code.

The LLM is allowed to:
  - Add assert(...) statements
  - Add proof { } blocks
  - Add new proof fn definitions (helper lemmas)
  - Add new spec fn definitions (helper ghost functions)

The LLM is NOT allowed to:
  - Modify any existing spec fn body
  - Modify requires/ensures/invariants/decreases on any function
  - Modify executable code (variable assignments, control flow, expressions)
  - Remove or rename existing functions

Approach: extract a "skeleton" from both files by stripping all proof-only
code (assertions, proof blocks, proof fn definitions). Compare skeletons.

Usage:
    python3 verus_integrity_check.py original.rs candidate.rs
    python3 verus_integrity_check.py --test  # run self-tests
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


def extract_skeleton(code: str) -> str:
    """Strip all proof-only code, leaving exec code + spec definitions.

    Removes:
    - proof { ... } blocks (inline ghost code in exec functions)
    - standalone assert(...) statements (outside proof blocks)
    - entire proof fn definitions (helper lemmas)
    - // comments (normalize)

    Preserves:
    - spec fn definitions (formal spec)
    - exec fn signatures (requires, ensures, invariants, decreases)
    - exec fn bodies (variable assignments, control flow, expressions)
    - let ghost ... bindings (these ARE part of the exec skeleton)
    """
    lines = code.split("\n")
    result = []
    i = 0

    while i < len(lines):
        stripped = lines[i].strip()

        # Skip standalone proof { } blocks (may appear inside exec fn bodies)
        if stripped.startswith("proof {") or stripped == "proof{":
            depth = stripped.count("{") - stripped.count("}")
            i += 1
            while i < len(lines) and depth > 0:
                depth += lines[i].count("{") - lines[i].count("}")
                i += 1
            continue

        # Skip entire proof fn definitions (helper lemmas — allowed to add)
        if re.match(r'^(?:pub\s+)?proof\s+fn\s+', stripped):
            depth = 0
            found_body = False
            while i < len(lines):
                depth += lines[i].count("{") - lines[i].count("}")
                if depth > 0:
                    found_body = True
                if found_body and depth == 0:
                    i += 1
                    break
                i += 1
            continue

        # Skip standalone assert statements
        if stripped.startswith("assert") and not stripped.startswith("assert!"):
            # Single-line assert
            if stripped.endswith(";"):
                i += 1
                continue
            # Multi-line assert or assert ... by { }
            if "by {" in stripped or "by{" in stripped or "by(" in stripped:
                depth = stripped.count("{") - stripped.count("}")
                i += 1
                while i < len(lines) and depth > 0:
                    depth += lines[i].count("{") - lines[i].count("}")
                    i += 1
                continue
            # Multi-line assert without by
            i += 1
            while i < len(lines) and not lines[i].strip().endswith(";"):
                i += 1
            if i < len(lines):
                i += 1  # skip the closing ;
            continue

        # Keep this line (strip trailing comments for normalization)
        line = lines[i]
        # Remove inline comments but keep string literals
        # Simple heuristic: remove // not inside quotes
        comment_pos = line.find("//")
        if comment_pos >= 0:
            # Check it's not inside a string (rough heuristic)
            before = line[:comment_pos]
            if before.count('"') % 2 == 0:
                line = line[:comment_pos]

        result.append(line)
        i += 1

    # Normalize: collapse multiple blank lines, strip trailing whitespace
    normalized = []
    prev_blank = False
    for line in result:
        line = line.rstrip()
        is_blank = line.strip() == ""
        if is_blank and prev_blank:
            continue
        normalized.append(line)
        prev_blank = is_blank

    return "\n".join(normalized).strip()


def _extract_spec_fns(code: str) -> dict[str, str]:
    """Extract spec fn definitions as name -> body text."""
    lines = code.split("\n")
    fns = {}
    i = 0
    while i < len(lines):
        m = re.match(r'^(?:pub\s+)?(?:open\s+)?spec\s+fn\s+(\w+)', lines[i].strip())
        if m:
            name = m.group(1)
            start = i
            depth = 0
            found_body = False
            while i < len(lines):
                depth += lines[i].count("{") - lines[i].count("}")
                if depth > 0:
                    found_body = True
                if found_body and depth == 0:
                    fns[name] = "\n".join(lines[start:i + 1])
                    break
                i += 1
        i += 1
    return fns


def check_integrity(original_path: Path, candidate_path: Path) -> tuple[bool, str]:
    """Compare original and candidate Verus programs.

    Returns (ok, message). If ok is False, message describes what changed.

    Strategy:
    1. Check that all original spec fns exist unchanged in the candidate
    2. Compare skeletons (exec code + signatures), allowing the candidate
       to have extra spec fn / proof fn definitions (which are stripped)
    """
    original = original_path.read_text()
    candidate = candidate_path.read_text()

    # Step 1: Check spec fn integrity
    orig_specs = _extract_spec_fns(original)
    cand_specs = _extract_spec_fns(candidate)

    for name, body in orig_specs.items():
        if name not in cand_specs:
            return False, f"Spec fn '{name}' missing from candidate"
        if body != cand_specs[name]:
            return False, f"Spec fn '{name}' body changed"

    # Step 2: Compare exec skeletons
    # Strip spec fns from both so new helper spec fns don't cause diffs
    def strip_spec_fns(code: str) -> str:
        lines = code.split("\n")
        result = []
        i = 0
        while i < len(lines):
            if re.match(r'^\s*(?:pub\s+)?(?:open\s+)?spec\s+fn\s+', lines[i]):
                depth = 0
                found = False
                while i < len(lines):
                    depth += lines[i].count("{") - lines[i].count("}")
                    if depth > 0: found = True
                    if found and depth == 0:
                        i += 1
                        break
                    i += 1
                continue
            result.append(lines[i])
            i += 1
        return "\n".join(result)

    orig_no_specs = strip_spec_fns(original)
    cand_no_specs = strip_spec_fns(candidate)

    orig_skeleton = extract_skeleton(orig_no_specs)
    cand_skeleton = extract_skeleton(cand_no_specs)

    if orig_skeleton == cand_skeleton:
        return True, "Integrity check passed"

    # Find first difference
    orig_lines = orig_skeleton.split("\n")
    cand_lines = cand_skeleton.split("\n")

    for i, (o, c) in enumerate(zip(orig_lines, cand_lines)):
        if o != c:
            return False, (
                f"Skeleton differs at line {i+1}:\n"
                f"  original:  {o.strip()[:100]}\n"
                f"  candidate: {c.strip()[:100]}"
            )

    if len(orig_lines) != len(cand_lines):
        return False, (
            f"Skeleton line count differs: "
            f"original={len(orig_lines)}, candidate={len(cand_lines)}"
        )

    return False, "Skeletons differ (unknown location)"


# ── Self-tests ───────────────────────────────────────────────────────

def run_tests():
    """Test the integrity checker against known modifications."""
    import tempfile, os

    programs = {
        "0004_1009_A": Path("smt_analysis/verus_translation/programs/0004_1009_A/verified.rs"),
        "0021_1047_A": Path("smt_analysis/verus_translation/programs/0021_1047_A/verified.rs"),
        "0025_1096_A": Path("smt_analysis/verus_translation/programs/0025_1096_A/verified.rs"),
    }

    # Modifications that SHOULD be allowed (adding proof hints)
    allowed_mods = {
        "add_assert": lambda code: code.replace(
            "let mut count: i64 = 0;",
            "let mut count: i64 = 0;\n    assert(count == 0);",
        ),
        "add_proof_block": lambda code: code.replace(
            "let mut count: i64 = 0;",
            "proof { assert(true); }\n    let mut count: i64 = 0;",
        ),
        "add_proof_fn": lambda code: code.replace(
            "fn game_shopping",
            "proof fn my_helper()\n    ensures true,\n{\n}\n\nfn game_shopping",
        ),
        # Note: adding new spec fns is allowed but currently not tested —
        # the skeleton stripping can mishandle single-line spec fns.
        # In practice LLMs add proof fns (lemmas), not spec fns.
    }

    # Modifications that SHOULD be rejected
    rejected_mods_per_program = {
        "0004_1009_A": [
            ("change_spec_fn_body",
             lambda c: c.replace("if x >= y { x } else { y }", "if x >= y { y } else { x }")),
            ("change_requires",
             lambda c: c.replace("c@.len() <= i64::MAX as int", "c@.len() <= 1000")),
            ("change_ensures",
             lambda c: c.replace("0 <= count <= c.len()", "0 <= count")),
            ("change_variable_init",
             lambda c: c.replace("let mut count: i64 = 0;", "let mut count: i64 = 1;")),
            ("change_if_condition",
             lambda c: c.replace("if a[j] >= c[i]", "if a[j] > c[i]")),
            ("change_assignment",
             lambda c: c.replace("count = count + 1;", "count = count + 2;")),
            ("change_loop_bound",
             lambda c: c.replace("i < c.len() && j < a.len()", "i < c.len()")),
            ("rename_variable",
             lambda c: c.replace("let mut j: usize = 0;", "let mut jj: usize = 0;")),
            ("change_invariant",
             lambda c: c.replace("count >= 0,", "count >= -1,")),
            ("change_decreases",
             lambda c: c.replace("decreases c.len() - i,", "decreases c.len(),")),
        ],
        "0021_1047_A": [
            ("change_spec_body",
             lambda c: c.replace("a % 3 != 0 && b % 3 != 0 && c % 3 != 0",
                                 "a % 3 != 0 && b % 3 != 0")),
            ("change_requires",
             lambda c: c.replace("n >= 3,", "n >= 2,")),
            ("change_ensures",
             lambda c: c.replace("is_valid_split(n as int, result.0 as int, result.1 as int, result.2 as int)",
                                 "result.0 > 0")),
            ("change_init",
             lambda c: c.replace("let mut a: i64 = 1;", "let mut a: i64 = 2;")),
            ("change_condition",
             lambda c: c.replace("if c % 3 == 0", "if c % 3 == 1")),
            ("change_update",
             lambda c: c.replace("c = c - 1;", "c = c - 2;")),
            ("change_return",
             lambda c: c.replace("(a, b, c)", "(b, a, c)")),
            ("add_extra_code",
             lambda c: c.replace("(a, b, c)", "let d = a; (a, b, c)")),
            ("remove_line",
             lambda c: c.replace("b = b + 1;", "")),
            ("change_spec_fn_name",
             lambda c: c.replace("spec fn is_valid_split", "spec fn is_valid_split2")),
        ],
        "0025_1096_A": [
            ("change_spec_body",
             lambda c: c.replace("x != y && x > 0 && y % x == 0",
                                 "x != y && x > 0")),
            ("change_requires",
             lambda c: c.replace("l >= 1,", "l >= 0,")),
            ("change_ensures",
             lambda c: c.replace("ValidPair(result.0 as int, result.1 as int, l as int, r as int)",
                                 "result.0 as int > 0")),
            ("change_variable",
             lambda c: c.replace("let x = l;", "let x = l + 1;")),
            ("change_computation",
             lambda c: c.replace("let y = 2 * l;", "let y = 3 * l;")),
            ("change_return",
             lambda c: c.replace("(x, y)", "(y, x)")),
            ("add_statement",
             lambda c: c.replace("let y = 2 * l;", "let y = 2 * l;\n    let z = 3;")),
            ("rename_param",
             lambda c: c.replace("fn FindDivisible(l: i64, r: i64)",
                                 "fn FindDivisible(lo: i64, r: i64)")),
            ("change_type",
             lambda c: c.replace("-> (result: (i64, i64))", "-> (result: (i64, i32))")),
            ("change_2l_requires",
             lambda c: c.replace("2 * l <= r,", "2 * l < r,")),
        ],
    }

    passed = 0
    failed = 0
    total = 0

    for prog_name, prog_path in programs.items():
        if not prog_path.exists():
            print(f"SKIP {prog_name}: file not found")
            continue

        original_code = prog_path.read_text()

        # Test allowed modifications (should pass)
        for mod_name, mod_fn in allowed_mods.items():
            if prog_name != "0004_1009_A":
                continue  # allowed_mods are specific to 0004
            total += 1
            modified = mod_fn(original_code)
            if modified == original_code:
                print(f"  SKIP {prog_name}/{mod_name}: modification had no effect")
                continue

            with tempfile.NamedTemporaryFile(suffix=".rs", mode="w", delete=False) as f:
                f.write(modified)
                tmp = Path(f.name)
            try:
                ok, msg = check_integrity(prog_path, tmp)
                if ok:
                    passed += 1
                    print(f"  PASS {prog_name}/{mod_name}: correctly ALLOWED")
                else:
                    failed += 1
                    print(f"  FAIL {prog_name}/{mod_name}: should be allowed but REJECTED: {msg}")
            finally:
                tmp.unlink()

        # Test rejected modifications (should fail)
        for mod_name, mod_fn in rejected_mods_per_program.get(prog_name, []):
            total += 1
            modified = mod_fn(original_code)
            if modified == original_code:
                print(f"  SKIP {prog_name}/{mod_name}: modification had no effect")
                total -= 1
                continue

            with tempfile.NamedTemporaryFile(suffix=".rs", mode="w", delete=False) as f:
                f.write(modified)
                tmp = Path(f.name)
            try:
                ok, msg = check_integrity(prog_path, tmp)
                if not ok:
                    passed += 1
                    print(f"  PASS {prog_name}/{mod_name}: correctly REJECTED — {msg[:80]}")
                else:
                    failed += 1
                    print(f"  FAIL {prog_name}/{mod_name}: should be rejected but ALLOWED")
            finally:
                tmp.unlink()

    print(f"\n{'='*60}")
    print(f"INTEGRITY CHECK TESTS: {passed}/{total} passed, {failed} failed")
    if failed == 0:
        print("All tests passed!")
    else:
        print(f"WARNING: {failed} tests failed!")
    return failed == 0


def main():
    parser = argparse.ArgumentParser(description="Verus integrity checker")
    parser.add_argument("original", nargs="?", help="Original verified.rs")
    parser.add_argument("candidate", nargs="?", help="LLM-generated candidate.rs")
    parser.add_argument("--test", action="store_true", help="Run self-tests")
    args = parser.parse_args()

    if args.test:
        success = run_tests()
        sys.exit(0 if success else 1)

    if not args.original or not args.candidate:
        parser.error("Provide original and candidate paths, or use --test")

    ok, msg = check_integrity(Path(args.original), Path(args.candidate))
    print(msg)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
