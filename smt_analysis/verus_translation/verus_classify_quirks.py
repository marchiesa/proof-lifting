#!/usr/bin/env python3
"""Classify essential assertions in Verus programs into paper categories A/B/C.

Verus equivalent of classify_quirks.py for Dafny.

Categories (from the paper):
  A. Missing axioms — sequence extensionality facts:
     A1. subrange-subrange: s.subrange(a,b).subrange(c,d) =~= s.subrange(...)
     A2. take-full: s.subrange(0, s.len()) =~= s  /  s.take(s.len()) =~= s
     A3. take-append: s.push(v).subrange(...) =~= ...
     A4. other seq extensionality (=~= involving Seq operations)

  B. E-matching gaps — trigger-related issues:
     B1. trigger forall: universally quantified fact not instantiated
     B2. trigger existential: existential needs a witness term
     B3. predicate/function instantiation: assert(P(args)) or reveal_with_fuel

  C. Brittleness — detected via seed variation (separate script)

  Other: nonlinear arithmetic (by(nonlinear_arith)), propagation, etc.

Pipeline:
  1. EXTRACT  — find assert statements in executable function bodies
  2. ABLATE   — remove each assertion, run verus, find essential ones
  3. CLASSIFY — pattern-match essential assertions into categories

Usage:
    python3 classify_quirks_verus.py --problem 0010_1043_A    # one problem
    python3 classify_quirks_verus.py --all                     # all stable programs
    python3 classify_quirks_verus.py --extract-only --problem X # just show parsed assertions
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent.resolve()
PROGRAMS_DIR = SCRIPT_DIR / "programs"
VERUS_BIN = "/tmp/verus_install/verus-arm64-macos/verus"
VERIFY_TIMEOUT = 60


# ── Phase 1: Extract assertions from executable function bodies ──────

def parse_function_spans(code: str) -> list[dict]:
    """Identify all function spans and their types (fn, proof fn, spec fn).

    Returns list of {name, kind, start_line, end_line} (0-indexed).
    """
    lines = code.split("\n")
    functions = []
    i = 0
    while i < len(lines):
        stripped = lines[i].strip()

        # Match function declarations
        # "fn name(...)", "proof fn name(...)", "spec fn name(...)",
        # "pub fn ...", "pub open spec fn ...", etc.
        m = re.match(
            r'^(?:pub\s+)?(?:open\s+)?(spec|proof|)\s*fn\s+(\w+)',
            stripped
        )
        if m:
            kind = m.group(1) or "exec"  # empty = executable fn
            name = m.group(2)

            # Find the opening brace for the function body
            # (might be on a later line after requires/ensures/decreases)
            j = i
            depth = 0
            found_body = False
            while j < len(lines):
                depth += lines[j].count("{") - lines[j].count("}")
                if depth > 0 and not found_body:
                    found_body = True
                if found_body and depth == 0:
                    functions.append({
                        "name": name,
                        "kind": kind,
                        "start_line": i,
                        "end_line": j,
                    })
                    break
                j += 1
            i = j + 1 if j < len(lines) else i + 1
        else:
            i += 1

    return functions


def find_assert_blocks(code: str) -> list[dict]:
    """Find all assert statements/blocks in Verus code.

    Handles:
    - assert(expr);
    - assert(expr) by { ... }
    - assert(expr) by(tactic) requires ...;
    - assert forall|...| ... implies ... by { ... };
    - proof { assert(...); ... } blocks (extracts the whole proof block)

    Returns list of {line, end_line, text, kind} (1-indexed lines).
    """
    lines = code.split("\n")
    blocks = []
    i = 0
    while i < len(lines):
        stripped = lines[i].strip()

        # Match "proof {" blocks (standalone proof blocks in exec functions)
        if stripped == "proof {" or stripped == "proof{":
            start = i
            depth = stripped.count("{") - stripped.count("}")
            j = i + 1
            while j < len(lines) and depth > 0:
                depth += lines[j].count("{") - lines[j].count("}")
                j += 1
            end = j - 1  # inclusive
            text = "\n".join(lines[start:end + 1])
            blocks.append({
                "line": start + 1,
                "end_line": end + 1,
                "text": text,
                "kind": "proof_block",
            })
            i = j
            continue

        # Match assert statements
        if stripped.startswith("assert") and not stripped.startswith("assert!"):
            start = i
            # Check for by { ... } block
            if "by {" in stripped or "by{" in stripped:
                depth = stripped.count("{") - stripped.count("}")
                j = i + 1
                while j < len(lines) and depth > 0:
                    depth += lines[j].count("{") - lines[j].count("}")
                    j += 1
                end = j - 1
            elif stripped.endswith(";"):
                end = i
            else:
                # Multi-line assert (e.g., assert forall spanning lines)
                j = i + 1
                while j < len(lines):
                    s = lines[j].strip()
                    if s.endswith(";") or s.endswith("};"):
                        break
                    if "by {" in s or "by{" in s:
                        # Start of by block
                        depth = s.count("{") - s.count("}")
                        j += 1
                        while j < len(lines) and depth > 0:
                            depth += lines[j].count("{") - lines[j].count("}")
                            j += 1
                        break
                    j += 1
                end = j

            text = " ".join(lines[k].strip() for k in range(start, end + 1))
            kind = "assert"
            if "by(nonlinear_arith)" in text or "by (nonlinear_arith)" in text:
                kind = "assert_nla"
            elif "by {" in text or "by{" in text:
                kind = "assert_by"
            elif "assert forall" in text:
                kind = "assert_forall"

            blocks.append({
                "line": start + 1,
                "end_line": end + 1,
                "text": text,
                "kind": kind,
            })
            i = end + 1
            continue

        i += 1

    return blocks


def extract_assertions(rs_path: Path) -> list[dict]:
    """Extract assertions from executable function bodies only.

    Skips assertions inside proof fn and spec fn.
    """
    code = rs_path.read_text()
    functions = parse_function_spans(code)
    all_asserts = find_assert_blocks(code)

    # Keep only assertions inside exec functions
    exec_fns = [f for f in functions if f["kind"] == "exec"]

    result = []
    for a in all_asserts:
        a_line = a["line"] - 1  # 0-indexed
        in_exec = any(
            f["start_line"] <= a_line <= f["end_line"]
            for f in exec_fns
        )
        if in_exec:
            a["index"] = len(result)
            result.append(a)

    return result


# ── Phase 2: Ablation ────────────────────────────────────────────────

def remove_assertion(code: str, assert_info: dict) -> str:
    """Comment out a single assertion/proof block."""
    lines = code.split("\n")
    start = assert_info["line"] - 1      # to 0-indexed
    end = assert_info["end_line"] - 1     # to 0-indexed
    for idx in range(start, end + 1):
        lines[idx] = "// REMOVED: " + lines[idx]
    return "\n".join(lines)


def verify_code(code: str, timeout: int = VERIFY_TIMEOUT) -> bool:
    """Verify Verus code. Returns True if 0 errors."""
    with tempfile.NamedTemporaryFile(suffix=".rs", mode="w", delete=False) as f:
        f.write(code)
        tmp_path = f.name
    try:
        r = subprocess.run(
            [VERUS_BIN, tmp_path, "--rlimit", str(timeout)],
            capture_output=True, text=True, timeout=timeout + 60,
        )
        output = r.stdout + "\n" + r.stderr
        return r.returncode == 0 and "0 errors" in output
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return False
    finally:
        os.unlink(tmp_path)


# ── Phase 3: Classification ──────────────────────────────────────────

# A: Missing axioms — sequence extensionality
A_PATTERNS = {
    "A1-subrange-subrange": [
        r'\.subrange\(.*\)\.subrange\(.*\)\s*=~=',
        r'=~=\s*\S+\.subrange\(.*\)\.subrange',
        r'\.take\(.*\)\.take\(.*\)\s*=~=',
        r'=~=\s*\S+\.take\(.*\)\.take',
    ],
    "A2-take-full": [
        r'\.subrange\(0.*len\(\).*\)\s*=~=',
        r'=~=\s*\S+\.subrange\(0.*len\(\)',
        r'\.take\(\S+\.len\(\).*\)\s*=~=',
        r'=~=\s*\S+\.take\(\S+\.len\(\)',
    ],
    "A3-push-subrange": [
        r'\.push\(.*\).*=~=',
        r'=~=.*\.push\(',
        r'\.subrange\(0.*\+\s*1\)\s*=~=.*\.subrange\(0',
        r'\.add\(.*\)\s*=~=',
        r'=~=.*\.add\(',
    ],
    "A4-other-seq-ext": [
        r'=~=',  # catch-all for any =~= not matched above
    ],
}

# B: E-matching gaps
B_PATTERNS = {
    "B1-trigger-forall": [
        r'assert\s+forall',
        r'assert\(\s*\w+\[.*\]\.len\(\)',   # assert(g[i].len() == ...) — length tracking
    ],
    "B2-trigger-existential": [
        r'assert.*exists',
    ],
    "B3-predicate-instantiation": [
        r'assert\(\s*[a-z_]\w+\(',        # assert(pred_name(args))
        r'reveal_with_fuel',               # function unfolding
    ],
}


def classify_assertion(text: str) -> dict:
    """Classify a single Verus assertion into categories."""
    text_stripped = text.strip()

    # NLA first (specific marker)
    if "nonlinear_arith" in text_stripped:
        return {"category": "other", "subcategory": "NLA",
                "confidence": "high"}

    # Check A patterns (sequence extensionality) — check specific before catch-all
    for cat in ["A1-subrange-subrange", "A2-take-full", "A3-push-subrange"]:
        for pat in A_PATTERNS[cat]:
            if re.search(pat, text_stripped):
                return {"category": "A", "subcategory": cat, "confidence": "high"}

    # A4 catch-all for any =~= not matched above
    if "=~=" in text_stripped:
        return {"category": "A", "subcategory": "A4-other-seq-ext",
                "confidence": "medium"}

    # Check B patterns
    for cat, patterns in B_PATTERNS.items():
        for pat in patterns:
            if re.search(pat, text_stripped):
                return {"category": "B", "subcategory": cat, "confidence": "medium"}

    # Proof block containing lemma calls
    if text_stripped.startswith("proof {"):
        # Check what's inside
        if "=~=" in text_stripped:
            return {"category": "A", "subcategory": "A4-other-seq-ext",
                    "confidence": "medium", "note": "=~= inside proof block"}
        if re.search(r'[a-z_]\w+\(', text_stripped):
            return {"category": "B", "subcategory": "B3-predicate-instantiation",
                    "confidence": "low", "note": "lemma call inside proof block"}

    return {"category": "needs_review", "subcategory": "unknown",
            "confidence": "low"}


# ── Main pipeline ────────────────────────────────────────────────────

def classify_problem(problem_name: str) -> dict:
    """Full classification for one Verus problem."""
    problem_dir = PROGRAMS_DIR / problem_name

    # Use verified_not_brittle.rs if available, else verified.rs
    rs_path = problem_dir / "verified_not_brittle.rs"
    if not rs_path.exists():
        rs_path = problem_dir / "verified.rs"
    if not rs_path.exists():
        return {"problem": problem_name, "error": "no verified.rs"}

    code = rs_path.read_text()
    asserts = extract_assertions(rs_path)

    if not asserts:
        return {
            "problem": problem_name,
            "source": rs_path.name,
            "total_assertions": 0,
            "essential_count": 0,
            "essential": [],
            "categories": {},
        }

    # Ablation: remove each assertion, check if verification breaks
    essential = []
    non_essential = []

    for a in asserts:
        variant = remove_assertion(code, a)
        passes = verify_code(variant)

        if not passes:
            a["essential"] = True
            classification = classify_assertion(a["text"])
            a["classification"] = classification
            essential.append(a)
        else:
            a["essential"] = False
            non_essential.append(a)

    # Aggregate categories
    categories = {}
    for a in essential:
        cat = a["classification"]["category"]
        sub = a["classification"]["subcategory"]
        if cat not in categories:
            categories[cat] = {}
        categories[cat][sub] = categories[cat].get(sub, 0) + 1

    return {
        "problem": problem_name,
        "source": rs_path.name,
        "total_assertions": len(asserts),
        "essential_count": len(essential),
        "non_essential_count": len(non_essential),
        "essential": essential,
        "categories": categories,
    }


def main():
    parser = argparse.ArgumentParser(description="Classify Verus SMT quirks")
    parser.add_argument("--problem", nargs="+", help="Specific problem(s)")
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--extract-only", action="store_true",
                        help="Only extract and show assertions, no ablation")
    parser.add_argument("--timeout", type=int, default=60)
    args = parser.parse_args()

    global VERIFY_TIMEOUT
    VERIFY_TIMEOUT = args.timeout

    # Load brittleness results to exclude brittle/failing programs
    brit_file = SCRIPT_DIR / "verus_brittleness_results.json"
    exclude = set()
    if brit_file.exists():
        brit = json.loads(brit_file.read_text())
        exclude = set(brit.get("brittle", []) + brit.get("always_fail", []))

    if args.problem:
        problems = args.problem
    elif args.all:
        problems = sorted(
            d.name for d in PROGRAMS_DIR.iterdir()
            if d.is_dir()
            and ((d / "verified.rs").exists() or (d / "verified_not_brittle.rs").exists())
            and d.name not in exclude
        )
    else:
        parser.error("Specify --problem or --all")

    if args.extract_only:
        for problem in problems:
            rs_path = PROGRAMS_DIR / problem / "verified_not_brittle.rs"
            if not rs_path.exists():
                rs_path = PROGRAMS_DIR / problem / "verified.rs"
            if not rs_path.exists():
                continue
            asserts = extract_assertions(rs_path)
            print(f"\n=== {problem} ({len(asserts)} assertions in exec fns) ===")
            for a in asserts:
                preview = a["text"][:120].replace("\n", " ")
                print(f"  L{a['line']}-{a['end_line']} [{a['kind']}]: {preview}")
        return

    print(f"Classifying {len(problems)} Verus problems (timeout={VERIFY_TIMEOUT}s)")
    print()

    all_results = {}
    total_essential = 0
    total_assertions = 0
    cat_totals = {}

    for i, problem in enumerate(problems):
        print(f"  [{i+1}/{len(problems)}] {problem}: ", end="", flush=True)
        t0 = time.time()
        r = classify_problem(problem)
        elapsed = round(time.time() - t0, 1)
        all_results[problem] = r

        ess = r.get("essential_count", 0)
        total_essential += ess
        total_assertions += r.get("total_assertions", 0)

        for cat, subs in r.get("categories", {}).items():
            for sub, count in subs.items():
                cat_totals[sub] = cat_totals.get(sub, 0) + count

        if ess > 0:
            cat_str = ", ".join(f"{k}:{v}" for k, v in r.get("categories", {}).items())
            print(f"{ess} essential / {r['total_assertions']} total — {cat_str} [{elapsed}s]")
        else:
            print(f"0 essential / {r.get('total_assertions', 0)} total [{elapsed}s]")

    # Summary
    print(f"\n{'='*60}")
    print(f"VERUS QUIRK CLASSIFICATION SUMMARY")
    print(f"{'='*60}")
    print(f"Programs:           {len(all_results)}")
    print(f"Total assertions:   {total_assertions}")
    print(f"Essential:          {total_essential}")
    print(f"Non-essential:      {total_assertions - total_essential}")
    print()
    print("By sub-category:")
    for sub, count in sorted(cat_totals.items()):
        print(f"  {sub}: {count}")

    # Save results
    output_path = SCRIPT_DIR / "verus_quirk_classification.json"
    output_path.write_text(json.dumps({
        "total_programs": len(all_results),
        "total_assertions": total_assertions,
        "total_essential": total_essential,
        "category_totals": cat_totals,
        "per_problem": all_results,
    }, indent=2, default=str))
    print(f"\nSaved to {output_path}")


if __name__ == "__main__":
    main()
