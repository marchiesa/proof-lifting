#!/usr/bin/env python3
"""
CVC5 ablation study: for each verified problem, check which assertions
are essential under CVC5 (vs Z3). Reuses the Z3 ablation's assertion
extraction and compares results.

Usage:
    # Run all verified problems with Z3 ablation data
    python3 smt_analysis/cvc5_ablation.py

    # Run specific problems
    python3 smt_analysis/cvc5_ablation.py 0006_1017_A 0009_1041_A

    # Parallel (default 4 workers)
    python3 smt_analysis/cvc5_ablation.py --workers 8

    # Just print aggregate summary from existing results
    python3 smt_analysis/cvc5_ablation.py --summary-only
"""
import argparse
import json
import re
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

PROJ_ROOT = Path(__file__).parent.parent.resolve()
RESULTS_DIR = PROJ_ROOT / "smt_analysis" / "results"
VERIFIED_LIST = RESULTS_DIR / "verified_problems.txt"

CVC5_PATH = "/opt/homebrew/bin/cvc5"
DAFNY = "dafny"
VERIFY_TIMEOUT = 60  # seconds per dafny verify


# ---------------------------------------------------------------------------
# Assertion extraction (mirrors ablate_and_diagnose.py)
# ---------------------------------------------------------------------------

def extract_asserts(dfy_path: Path) -> list[dict]:
    """Extract top-level assert statements, handling multi-line and by-blocks."""
    lines = dfy_path.read_text().splitlines()
    blocks = []
    i = 0
    while i < len(lines):
        stripped = lines[i].strip()
        if stripped.startswith("assert "):
            start = i
            if "by {" in stripped:
                depth = stripped.count("{") - stripped.count("}")
                j = i + 1
                while j < len(lines) and depth > 0:
                    depth += lines[j].count("{") - lines[j].count("}")
                    j += 1
                end = j - 1
            elif stripped.endswith(";"):
                end = i
            else:
                j = i + 1
                while j < len(lines) and not lines[j].strip().endswith(";"):
                    j += 1
                end = j
            text = " ".join(lines[k].strip() for k in range(start, end + 1))
            blocks.append({
                "index": len(blocks),
                "line": start + 1,
                "line_idx": start,
                "end_idx": end,
                "text": text,
            })
        i += 1

    # Filter out nested asserts (inside by-blocks)
    toplevel = []
    for b in blocks:
        inside = any(
            o["line_idx"] < b["line_idx"] and b["end_idx"] <= o["end_idx"]
            for o in blocks if o is not b
        )
        if not inside:
            toplevel.append(b)
    for idx, b in enumerate(toplevel):
        b["index"] = idx
    return toplevel


def create_variant(dfy_path: Path, assert_info: dict) -> str:
    """Return file content with one assert block removed."""
    lines = dfy_path.read_text().splitlines(keepends=True)
    start = assert_info["line_idx"]
    end = assert_info.get("end_idx", start)
    for idx in range(start, end + 1):
        lines[idx] = f"// REMOVED: {lines[idx]}"
    return "".join(lines)


# ---------------------------------------------------------------------------
# Verification
# ---------------------------------------------------------------------------

def verify_cvc5(dfy_content: str, timeout: int = VERIFY_TIMEOUT) -> dict:
    """Verify with CVC5. Returns {verified, time, model_crash}."""
    with tempfile.NamedTemporaryFile(suffix=".dfy", mode="w", delete=False) as f:
        f.write(dfy_content)
        tmp_path = f.name

    cmd = [DAFNY, "verify", tmp_path, "--allow-warnings",
           "--verification-time-limit", str(timeout),
           "--solver-path", CVC5_PATH,
           "--boogie", "/proverOpt:SOLVER=CVC5"]

    t0 = time.time()
    try:
        result = subprocess.run(cmd, capture_output=True, text=True,
                                timeout=timeout + 60)
        elapsed = time.time() - t0
        output = result.stdout + result.stderr
    except subprocess.TimeoutExpired:
        elapsed = time.time() - t0
        output = "PROCESS TIMEOUT"

    Path(tmp_path).unlink(missing_ok=True)

    m = re.search(r"(\d+) verified, (\d+) errors?(?:, (\d+) time out)?", output)
    has_model_crash = "BadExprFromProver" in output

    if m:
        verified = int(m.group(1))
        errors = int(m.group(2))
        timeouts = int(m.group(3)) if m.group(3) else 0
    else:
        verified = 0
        errors = -1
        timeouts = 0

    return {
        "verified": verified,
        "errors": errors,
        "timeouts": timeouts,
        "time": round(elapsed, 1),
        "model_crash": has_model_crash,
    }


# ---------------------------------------------------------------------------
# Per-problem ablation
# ---------------------------------------------------------------------------

def run_problem(problem_id: str, verbose: bool = False) -> dict:
    """Run CVC5 ablation on one problem. Returns result dict."""
    results_dir = RESULTS_DIR / problem_id
    verified_dfy = results_dir / "verified.dfy"
    z3_ablation_file = results_dir / "ablation" / "results.json"

    if not verified_dfy.exists():
        return {"problem": problem_id, "error": "no verified.dfy"}

    # Load Z3 ablation for comparison
    z3_essential = {}
    if z3_ablation_file.exists():
        z3_data = json.loads(z3_ablation_file.read_text())
        for r in z3_data.get("results", []):
            z3_essential[r["line"]] = r.get("essential", False)

    # Extract assertions
    assertions = extract_asserts(verified_dfy)
    if not assertions:
        return {
            "problem": problem_id,
            "total_assertions": 0,
            "baseline": {"verified": -1},
            "results": [],
            "summary": {"total": 0, "cvc5_essential": 0, "z3_essential": 0,
                         "both": 0, "z3_only": 0, "cvc5_only": 0},
        }

    # CVC5 baseline
    baseline = verify_cvc5(verified_dfy.read_text())
    baseline_verified = baseline["verified"]

    if verbose:
        print(f"  [{problem_id}] baseline: {baseline_verified} verified, "
              f"{len(assertions)} assertions")

    # Ablate each assertion
    ablation_results = []
    for a in assertions:
        content = create_variant(verified_dfy, a)
        result = verify_cvc5(content)

        cvc5_essential = result["verified"] < baseline_verified
        z3_ess = z3_essential.get(a["line"], None)

        ablation_results.append({
            "index": a["index"],
            "line": a["line"],
            "text": a["text"],
            "cvc5_verified": result["verified"],
            "cvc5_baseline": baseline_verified,
            "cvc5_essential": cvc5_essential,
            "cvc5_time": result["time"],
            "z3_essential": z3_ess,
        })

    # Compute summary
    z3_ess_count = sum(1 for r in ablation_results if r["z3_essential"] is True)
    cvc5_ess_count = sum(1 for r in ablation_results if r["cvc5_essential"])
    both = sum(1 for r in ablation_results
               if r["z3_essential"] is True and r["cvc5_essential"])
    z3_only = sum(1 for r in ablation_results
                  if r["z3_essential"] is True and not r["cvc5_essential"])
    cvc5_only = sum(1 for r in ablation_results
                    if r["z3_essential"] is not True and r["cvc5_essential"])

    out = {
        "problem": problem_id,
        "total_assertions": len(ablation_results),
        "baseline": baseline,
        "results": ablation_results,
        "summary": {
            "total": len(ablation_results),
            "z3_essential": z3_ess_count,
            "cvc5_essential": cvc5_ess_count,
            "both": both,
            "z3_only": z3_only,
            "cvc5_only": cvc5_only,
        },
    }

    # Save per-problem result
    output_file = results_dir / "cvc5_ablation.json"
    output_file.write_text(json.dumps(out, indent=2))

    status = "OK"
    if baseline.get("model_crash"):
        status = "OK (model crash in baseline)"
    print(f"  {problem_id}: {status} — "
          f"Z3={z3_ess_count} CVC5={cvc5_ess_count} both={both} "
          f"Z3only={z3_only} CVC5only={cvc5_only}")

    return out


# ---------------------------------------------------------------------------
# Aggregate summary
# ---------------------------------------------------------------------------

def print_aggregate(all_results: list[dict]):
    """Print aggregate summary across all problems."""
    problems_with_data = [r for r in all_results if "summary" in r]

    total_assertions = sum(r.get("total_assertions", r["summary"].get("total", 0))
                           for r in problems_with_data)
    def _s(r, key, alt=None):
        """Get summary value, trying alternate key names for old format."""
        s = r["summary"]
        if key in s:
            return s[key]
        if alt and alt in s:
            return s[alt]
        return 0

    total_z3_ess = sum(_s(r, "z3_essential") for r in problems_with_data)
    total_cvc5_ess = sum(_s(r, "cvc5_essential") for r in problems_with_data)
    total_both = sum(_s(r, "both", "both_essential") for r in problems_with_data)
    total_z3_only = sum(_s(r, "z3_only") for r in problems_with_data)
    total_cvc5_only = sum(_s(r, "cvc5_only") for r in problems_with_data)

    problems_with_z3_ess = sum(1 for r in problems_with_data if r["summary"]["z3_essential"] > 0)
    problems_with_cvc5_ess = sum(1 for r in problems_with_data if r["summary"]["cvc5_essential"] > 0)

    print()
    print("=" * 60)
    print("AGGREGATE CVC5 vs Z3 ABLATION RESULTS")
    print("=" * 60)
    print(f"Problems analyzed:           {len(problems_with_data)}")
    print(f"Total assertions:            {total_assertions}")
    print()
    print(f"Z3 essential:                {total_z3_ess} (across {problems_with_z3_ess} problems)")
    print(f"CVC5 essential:              {total_cvc5_ess} (across {problems_with_cvc5_ess} problems)")
    print(f"Essential in both:           {total_both}")
    print(f"Z3-only (Z3 quirk, not CVC5): {total_z3_only}")
    print(f"CVC5-only (CVC5 quirk, not Z3): {total_cvc5_only}")

    if total_z3_ess > 0:
        pct_shared = round(total_both / total_z3_ess * 100, 1)
        pct_z3_only = round(total_z3_only / total_z3_ess * 100, 1)
        print()
        print(f"Of Z3's {total_z3_ess} essential assertions:")
        print(f"  {pct_shared}% also essential for CVC5")
        print(f"  {pct_z3_only}% Z3-specific (CVC5 doesn't need them)")

    # Save aggregate
    aggregate_file = RESULTS_DIR / "cvc5_ablation_aggregate.json"
    aggregate_file.write_text(json.dumps({
        "problems_analyzed": len(problems_with_data),
        "total_assertions": total_assertions,
        "z3_essential": total_z3_ess,
        "cvc5_essential": total_cvc5_ess,
        "both_essential": total_both,
        "z3_only": total_z3_only,
        "cvc5_only": total_cvc5_only,
        "per_problem": [
            {"problem": r["problem"], **r["summary"]}
            for r in problems_with_data
        ],
    }, indent=2))
    print(f"\nAggregate saved to {aggregate_file}")


def load_existing_results() -> list[dict]:
    """Load all existing cvc5_ablation.json files."""
    results = []
    verified = [l.strip() for l in VERIFIED_LIST.read_text().splitlines() if l.strip()]
    for p in verified:
        f = RESULTS_DIR / p / "cvc5_ablation.json"
        if f.exists():
            results.append(json.loads(f.read_text()))
    return results


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="CVC5 ablation study")
    parser.add_argument("problems", nargs="*", help="Specific problem IDs (default: all verified with Z3 ablation)")
    parser.add_argument("--workers", type=int, default=4, help="Parallel workers")
    parser.add_argument("--summary-only", action="store_true", help="Just print aggregate from existing results")
    parser.add_argument("--timeout", type=int, default=60, help="Verify timeout per assertion")
    args = parser.parse_args()

    global VERIFY_TIMEOUT
    VERIFY_TIMEOUT = args.timeout

    if args.summary_only:
        results = load_existing_results()
        print_aggregate(results)
        return

    # Determine which problems to run
    if args.problems:
        problems = args.problems
    else:
        verified = [l.strip() for l in VERIFIED_LIST.read_text().splitlines() if l.strip()]
        problems = []
        for p in verified:
            verified_dfy = RESULTS_DIR / p / "verified.dfy"
            if verified_dfy.exists():
                # Skip if already done
                cvc5_result = RESULTS_DIR / p / "cvc5_ablation.json"
                if cvc5_result.exists():
                    continue
                problems.append(p)

    if not problems:
        print("No problems to run (all done?). Use --summary-only for aggregate.")
        results = load_existing_results()
        if results:
            print_aggregate(results)
        return

    print(f"CVC5 ablation: {len(problems)} problems, {args.workers} workers")
    print()

    all_results = load_existing_results()  # include previously completed

    if args.workers == 1:
        for p in problems:
            r = run_problem(p, verbose=True)
            all_results.append(r)
    else:
        with ThreadPoolExecutor(max_workers=args.workers) as executor:
            futures = {executor.submit(run_problem, p): p for p in problems}
            for future in as_completed(futures):
                name = futures[future]
                try:
                    r = future.result()
                    all_results.append(r)
                except Exception as e:
                    print(f"  {name}: ERROR — {e}")

    print_aggregate(all_results)


if __name__ == "__main__":
    main()
