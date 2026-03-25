#!/usr/bin/env python3
"""
Seed variation experiment: for each of the 40 problems with essential assertions,
run dafny verify with N different random seeds and report pass/fail per seed.

Usage:
    python3 smt_analysis/seed_variation.py --seeds 10 --workers 6
    python3 smt_analysis/seed_variation.py --seeds 10 --names 0000_1013_A 0006_1017_A
"""

import argparse
import json
import subprocess
import sys
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

PROJ_ROOT = Path(__file__).parent.parent.resolve()
RESULTS_DIR = PROJ_ROOT / "smt_analysis" / "results"
SEEDS = list(range(10))  # 0..9


def verify_with_seed(dfy_path: Path, seed: int, timeout: int = 60) -> dict:
    """Run dafny verify with a specific random seed. Returns {seed, passed, output}."""
    try:
        r = subprocess.run(
            ["dafny", "verify", str(dfy_path),
             "--boogie", f"-randomSeed:{seed}",
             "--verification-time-limit", str(timeout)],
            capture_output=True, text=True, timeout=timeout + 30,
        )
        output = r.stdout + r.stderr
        passed = "0 errors" in output and "verified" in output
        timed_out = "timed out" in output.lower()
        return {"seed": seed, "passed": passed, "timed_out": timed_out, "exit_code": r.returncode}
    except subprocess.TimeoutExpired:
        return {"seed": seed, "passed": False, "timed_out": True, "exit_code": -1}


def run_problem(name: str, seeds: list[int], timeout: int) -> dict:
    """Run seed variation for one problem. Returns summary dict."""
    verified_path = RESULTS_DIR / name / "verified.dfy"
    if not verified_path.exists():
        return {"problem": name, "error": "verified.dfy not found"}

    results = []
    for seed in seeds:
        r = verify_with_seed(verified_path, seed, timeout)
        results.append(r)
        status = "PASS" if r["passed"] else ("TIMEOUT" if r["timed_out"] else "FAIL")
        print(f"  {name}  seed={seed}  {status}")

    n_pass = sum(1 for r in results if r["passed"])
    n_total = len(results)
    brittle = n_pass < n_total
    return {
        "problem": name,
        "seeds_passed": n_pass,
        "seeds_total": n_total,
        "pass_rate": round(n_pass / n_total, 2),
        "brittle": brittle,
        "per_seed": results,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seeds", type=int, default=10, help="Number of seeds (0..N-1)")
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--names", nargs="+", help="Specific problem names to test")
    parser.add_argument("--output", default="smt_analysis/results/seed_variation.json")
    args = parser.parse_args()

    seeds = list(range(args.seeds))

    # Load the 40 problems with essential assertions from diagnosis_summary
    summary_path = RESULTS_DIR / "diagnosis_summary.json"
    summary = json.loads(summary_path.read_text())
    all_problems = sorted(set(d["problem"] for d in summary["all_diagnoses"]))

    if args.names:
        problems = [n for n in args.names if n in all_problems]
        missing = set(args.names) - set(all_problems)
        if missing:
            print(f"Warning: not in essential-assertion set: {missing}", file=sys.stderr)
    else:
        problems = all_problems

    print(f"Running seed variation: {len(problems)} problems, {len(seeds)} seeds each")
    print(f"Seeds: {seeds}")
    print()

    all_results = []

    # Run problems in parallel (each problem sequentially over seeds)
    with ProcessPoolExecutor(max_workers=args.workers) as ex:
        futures = {ex.submit(run_problem, name, seeds, args.timeout): name for name in problems}
        for fut in as_completed(futures):
            result = fut.result()
            all_results.append(result)

    all_results.sort(key=lambda r: r["problem"])

    # Summary stats
    brittle = [r for r in all_results if r.get("brittle")]
    stable  = [r for r in all_results if not r.get("brittle") and "error" not in r]

    print()
    print("=" * 60)
    print(f"RESULTS: {len(problems)} problems, {len(seeds)} seeds")
    print(f"  Brittle (at least 1 seed fails): {len(brittle)}")
    print(f"  Stable  (all seeds pass):        {len(stable)}")
    print()
    if brittle:
        print("Brittle problems (pass_rate < 1.0):")
        for r in sorted(brittle, key=lambda x: x["pass_rate"]):
            print(f"  {r['problem']:25s}  {r['seeds_passed']}/{r['seeds_total']} seeds pass  ({r['pass_rate']*100:.0f}%)")

    output = {
        "seeds": seeds,
        "n_problems": len(problems),
        "n_brittle": len(brittle),
        "n_stable": len(stable),
        "results": all_results,
    }
    out_path = PROJ_ROOT / args.output
    out_path.write_text(json.dumps(output, indent=2))
    print(f"\nResults written to {out_path}")


if __name__ == "__main__":
    main()
