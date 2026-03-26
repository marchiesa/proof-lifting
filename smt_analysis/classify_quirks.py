#!/usr/bin/env python3
"""Classify essential assertions into paper categories A/B/C.

Categories (from the paper):
  A. Missing axioms — sequence extensionality facts with no direct axiom:
     A1. take-take: s[..n][..m] == s[..m] when m <= n
     A2. take-full: s[..|s|] == s
     A3. take-append: (s+t)[..n] == s[..n] if n<=|s|, or s + t[..n-|s|] if n>|s|
         Also: s[..i+1] == s[..i] + [s[i]]  (take-append variant)
     A4. append-empty: s + [] == [] + s == s
     A5. other sequence equality (multiset, split-concat, etc.)

  B. E-matching gaps — trigger-related issues:
     B1. trigger forall: a universally quantified fact is not instantiated
     B2. trigger existential: an existential needs a witness term

  C. Brittleness — proofs sensitive to solver heuristics:
     C1. seed-sensitive: verification fails with some random seeds
     C2. long chain: sequence of intermediate assertions guiding the solver

  Other: NLA, propagation, unclassified

Usage:
    python3 classify_quirks.py                    # classify all
    python3 classify_quirks.py --problem X        # classify one
    python3 classify_quirks.py --brittleness-only # just run seed tests
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent.resolve()
RESULTS_DIR = SCRIPT_DIR / "results"

DOTNET = os.environ.get("DOTNET8",
    "/opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet")
DAFNY_DLL = os.environ.get("DAFNY_DLL",
    str(SCRIPT_DIR.parent / "dafny-source" / "Binaries" / "Dafny.dll"))
VERIFY_TIMEOUT = 60
NUM_SEEDS = 10


# ── Pattern-based classification ──────────────────────────────────────

# A: Missing axioms — sequence extensionality patterns
A_PATTERNS = {
    "A1-take-take": [
        r'\[\.\..*\]\[\.\..*\]\s*==',    # s[..n][..m] == ...
        r'==\s*\w+\[\.\..*\]\[\.\..*\]',  # ... == s[..n][..m]
    ],
    "A2-take-full": [
        r'\[\.\.[\|]\w+[\|]\]\s*==\s*\w+',   # s[..|s|] == s
        r'\w+\s*==\s*\w+\[\.\.[\|]\w+[\|]\]', # s == s[..|s|]
        r'\[\.\.n\]\s*==',                      # a[..n] == a (common variant)
    ],
    "A3-take-append": [
        r'\[\.\..*\+\s*1\]\s*==\s*\w+\[\.\..*\]\s*\+\s*\[',  # s[..i+1] == s[..i] + [s[i]]
        r'\+\s*\[\w+\[.*\]\]\s*==\s*\w+\[\.\..*\+\s*1\]',    # s[..i] + [s[i]] == s[..i+1]
    ],
    "A4-append-empty": [
        r'\+\s*\[\]\s*==',   # s + [] == ...
        r'==\s*.*\+\s*\[\]', # ... == s + []
    ],
    "A5-other-seq": [
        r'multiset\(',       # multiset equality
        r'\[.*\.\.\]\s*==',  # s[i..] == ...
    ],
}

# B: E-matching gaps
B_PATTERNS = {
    "B1-trigger-forall": [
        r'assert\s+forall',           # re-asserting a forall
        r'assert\s+\|\w+\|\s*==',     # assert |s| == k (length tracking)
    ],
    "B2-trigger-existential": [
        r'assert\s+exists',           # explicit existential
        # Function call providing witness (predicate at specific args)
        r'assert\s+\w+\(',            # assert Predicate(args) — could be witness
    ],
}


def classify_assertion(text: str, context_lines: list[str] = []) -> dict:
    """Classify a single assertion text into categories."""
    text_stripped = text.strip()

    # Check A patterns first (sequence extensionality)
    for cat, patterns in A_PATTERNS.items():
        for pat in patterns:
            if re.search(pat, text_stripped):
                return {"category": "A", "subcategory": cat, "confidence": "high"}

    # Check B patterns (e-matching)
    for cat, patterns in B_PATTERNS.items():
        for pat in patterns:
            if re.search(pat, text_stripped):
                return {"category": "B", "subcategory": cat, "confidence": "medium"}

    # B2 heuristic: assert Predicate(specific, args) — likely witness
    if re.match(r'assert\s+[A-Z]\w+\(', text_stripped):
        return {"category": "B", "subcategory": "B2-trigger-existential",
                "confidence": "medium", "note": "predicate call — likely witness"}

    # NLA heuristic
    if re.search(r'\*\s*\w+\s*(<=|>=|==|<|>)', text_stripped) or \
       re.search(r'(<=|>=|==|<|>)\s*\w+\s*\*', text_stripped):
        if re.search(r'[a-z_]\w*\s*\*\s*[a-z_]\w*', text_stripped):
            return {"category": "other", "subcategory": "NLA",
                    "confidence": "medium"}

    return {"category": "unclassified", "subcategory": "unknown",
            "confidence": "low"}


# ── Brittleness detection ─────────────────────────────────────────────

def verify_with_seed(dfy_path: Path, seed: int, timeout: int = VERIFY_TIMEOUT) -> bool:
    """Run dafny verify with a specific random seed."""
    cmd = [DOTNET, DAFNY_DLL, "verify", str(dfy_path),
           "--verification-time-limit", str(timeout),
           "--boogie", f"/proverOpt:O:smt.random_seed={seed}"]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True,
                          timeout=timeout + 60)
        return "0 errors" in r.stdout
    except:
        return False


def check_brittleness(dfy_path: Path, num_seeds: int = NUM_SEEDS) -> dict:
    """Check if a program is brittle by running with different seeds in parallel."""
    import concurrent.futures

    def run_seed(seed):
        return seed, verify_with_seed(dfy_path, seed)

    results = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=num_seeds) as executor:
        futures = [executor.submit(run_seed, s) for s in range(num_seeds)]
        for f in concurrent.futures.as_completed(futures):
            seed, ok = f.result()
            results[seed] = ok

    passes = sum(1 for v in results.values() if v)
    return {
        "total_seeds": num_seeds,
        "passes": passes,
        "fails": num_seeds - passes,
        "is_brittle": 0 < passes < num_seeds,
        "always_passes": passes == num_seeds,
        "always_fails": passes == 0,
        "per_seed": results,
    }


# ── Ablation with classification ──────────────────────────────────────

def find_assertions_ast(problem_dir: Path) -> list[dict]:
    """Find assertions using the AST mapping if available."""
    ast_path = problem_dir / "artifacts" / "ast_mapping.json"
    dfy_path = problem_dir / "verified.dfy"

    if not dfy_path.exists():
        return []

    code = dfy_path.read_text()
    asserts = []
    lines = code.split("\n")
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith("assert ") and ";" in stripped:
            asserts.append({
                "line": i + 1,
                "text": stripped,
                "indent": len(line) - len(line.lstrip()),
            })
    return asserts


def remove_assertion(code: str, line_num: int) -> str:
    """Comment out a single assertion by line number."""
    lines = code.split("\n")
    idx = line_num - 1
    # Handle assert ... by { } blocks
    stripped = lines[idx].strip()
    if stripped.startswith("assert "):
        lines[idx] = "// REMOVED: " + lines[idx].lstrip()
        # Check for by { } block
        if stripped.endswith("{") or (idx + 1 < len(lines) and lines[idx+1].strip() == "{"):
            depth = 0
            for j in range(idx, len(lines)):
                depth += lines[j].count("{") - lines[j].count("}")
                if j > idx:
                    lines[j] = "// REMOVED: " + lines[j].lstrip()
                if depth <= 0:
                    break
    return "\n".join(lines)


def verify_code(code: str, tmp_path: Path, timeout: int = VERIFY_TIMEOUT) -> bool:
    """Verify a Dafny program."""
    tmp_path.write_text(code)
    cmd = [DOTNET, DAFNY_DLL, "verify", str(tmp_path),
           "--verification-time-limit", str(timeout)]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True,
                          timeout=timeout + 60)
        return "0 errors" in r.stdout
    except:
        return False


def classify_problem(problem_name: str, check_brittle: bool = True) -> dict:
    """Full classification for one problem."""
    problem_dir = RESULTS_DIR / problem_name
    dfy_path = problem_dir / "verified.dfy"

    if not dfy_path.exists():
        return {"problem": problem_name, "error": "no verified.dfy"}

    code = dfy_path.read_text()
    asserts = find_assertions_ast(problem_dir)

    if not asserts:
        return {"problem": problem_name, "total_assertions": 0,
                "essential": [], "categories": {}}

    tmp = problem_dir / "tmp_classify.dfy"

    # Ablation: remove each assertion and check
    essential = []
    non_essential = []

    for a in asserts:
        stripped_code = remove_assertion(code, a["line"])
        ok = verify_code(stripped_code, tmp)
        classification = classify_assertion(a["text"])
        a["classification"] = classification

        if not ok:
            a["essential"] = True
            essential.append(a)
        else:
            a["essential"] = False
            non_essential.append(a)

    # Brittleness check on essential assertions
    # For each essential assertion, we already know it fails with default seed.
    # Check if it fails with ALL seeds (truly essential) or only some (brittle).
    if check_brittle and essential:
        for a in essential:
            stripped_code = remove_assertion(code, a["line"])
            # Write to a unique tmp file per assertion to avoid conflicts
            tmp_brit = problem_dir / f"tmp_brit_{a['line']}.dfy"
            tmp_brit.write_text(stripped_code)
            brit = check_brittleness(tmp_brit, num_seeds=NUM_SEEDS)
            a["brittleness"] = brit
            tmp_brit.unlink(missing_ok=True)
            if brit["is_brittle"]:
                # Override classification — this is a brittle proof
                a["classification"]["category"] = "C"
                a["classification"]["subcategory"] = "C1-seed-sensitive"
                a["classification"]["confidence"] = "high"
                a["classification"]["note"] = f"passes {brit['passes']}/{brit['total_seeds']} seeds"

    tmp.unlink(missing_ok=True)

    # Aggregate categories
    categories = {}
    for a in essential:
        cat = a["classification"]["category"]
        sub = a["classification"]["subcategory"]
        categories.setdefault(cat, {}).setdefault(sub, 0)
        categories[cat][sub] += 1

    return {
        "problem": problem_name,
        "total_assertions": len(asserts),
        "essential_count": len(essential),
        "non_essential_count": len(non_essential),
        "essential": essential,
        "categories": categories,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--problem", nargs="+")
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--no-brittleness", action="store_true")
    parser.add_argument("--brittleness-only", action="store_true")
    parser.add_argument("--seeds", type=int, default=10)
    parser.add_argument("--timeout", type=int, default=60)
    args = parser.parse_args()

    global NUM_SEEDS, VERIFY_TIMEOUT
    NUM_SEEDS = args.seeds
    VERIFY_TIMEOUT = args.timeout

    if args.problem:
        problems = args.problem
    else:
        problems = [l.strip() for l in
                    (RESULTS_DIR / "verified_problems.txt").read_text().splitlines()
                    if l.strip()]

    if args.limit:
        problems = problems[:args.limit]

    print(f"Classifying {len(problems)} problems (seeds={NUM_SEEDS}, timeout={VERIFY_TIMEOUT}s)")

    all_results = []
    total_A = 0
    total_B = 0
    total_C = 0
    total_other = 0
    total_essential = 0

    for i, prob in enumerate(problems):
        print(f"[{i+1}/{len(problems)}] {prob}...")
        r = classify_problem(prob, check_brittle=not args.no_brittleness)
        all_results.append(r)

        ess = r.get("essential_count", 0)
        total_essential += ess
        for a in r.get("essential", []):
            cat = a["classification"]["category"]
            if cat == "A": total_A += 1
            elif cat == "B": total_B += 1
            elif cat == "C": total_C += 1
            else: total_other += 1

        if ess > 0:
            cats = r.get("categories", {})
            cat_str = ", ".join(f"{k}:{sum(v.values())}" for k, v in cats.items())
            print(f"  {ess} essential — {cat_str}")

    # Summary
    print(f"\n{'='*60}")
    print(f"CLASSIFICATION SUMMARY")
    print(f"{'='*60}")
    print(f"Total essential: {total_essential}")
    print(f"  A (missing axioms): {total_A}")
    print(f"  B (e-matching):     {total_B}")
    print(f"  C (brittleness):    {total_C}")
    print(f"  Other:              {total_other}")

    # Save
    out = RESULTS_DIR / "classification_results.json"
    out.write_text(json.dumps(all_results, indent=2, default=str))
    print(f"\nSaved to {out}")


if __name__ == "__main__":
    main()
