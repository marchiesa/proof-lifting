#!/usr/bin/env python3
"""Check which Verus programs are brittle (seed-sensitive).

Runs each verified.rs with multiple Z3 random seeds via --smt-option.
A program is "brittle" if it passes with some seeds and fails with others.

Usage:
    python3 check_brittleness.py                   # check all
    python3 check_brittleness.py --problem 0000_1013_A
    python3 check_brittleness.py --seeds 20        # more seeds
    python3 check_brittleness.py --workers 8       # parallelism across problems
"""
from __future__ import annotations

import argparse
import json
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent.resolve()
PROGRAMS_DIR = SCRIPT_DIR / "programs"
VERUS_BIN = "/tmp/verus_install/verus-arm64-macos/verus"
VERIFY_TIMEOUT = 60
NUM_SEEDS = 10


def verify_with_seed(rs_path: Path, seed: int, timeout: int = VERIFY_TIMEOUT) -> bool:
    """Run verus on a file with a specific Z3 random seed."""
    try:
        r = subprocess.run(
            [VERUS_BIN, str(rs_path),
             "--smt-option", f"smt.random_seed={seed}",
             "--rlimit", str(timeout)],
            capture_output=True, text=True, timeout=timeout + 60,
        )
        output = r.stdout + "\n" + r.stderr
        return r.returncode == 0 and "0 errors" in output
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return False


def check_brittleness(rs_path: Path, num_seeds: int = NUM_SEEDS) -> dict:
    """Check if a Verus program is brittle by running with different seeds."""

    def run_seed(seed):
        return seed, verify_with_seed(rs_path, seed)

    results = {}
    with ThreadPoolExecutor(max_workers=num_seeds) as executor:
        futures = [executor.submit(run_seed, s) for s in range(num_seeds)]
        for f in as_completed(futures):
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


def main():
    parser = argparse.ArgumentParser(description="Check Verus brittleness")
    parser.add_argument("--problem", nargs="+", help="Specific problem(s)")
    parser.add_argument("--seeds", type=int, default=10)
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--workers", type=int, default=1,
                        help="Parallelism across problems (seeds are already parallel)")
    args = parser.parse_args()

    global NUM_SEEDS, VERIFY_TIMEOUT
    NUM_SEEDS = args.seeds
    VERIFY_TIMEOUT = args.timeout

    # Find all verified programs
    if args.problem:
        problems = args.problem
    else:
        problems = sorted(
            d.name for d in PROGRAMS_DIR.iterdir()
            if d.is_dir() and (d / "verified.rs").exists()
        )

    print(f"Brittleness check: {len(problems)} programs, {NUM_SEEDS} seeds each")
    print(f"Verus binary: {VERUS_BIN}")
    print()

    results = {}
    brittle = []
    stable = []
    always_fail = []

    for i, problem in enumerate(problems):
        rs_path = PROGRAMS_DIR / problem / "verified.rs"
        if not rs_path.exists():
            print(f"  [{i+1}/{len(problems)}] {problem}: SKIP (no verified.rs)")
            continue

        print(f"  [{i+1}/{len(problems)}] {problem}: ", end="", flush=True)
        t0 = time.time()
        brit = check_brittleness(rs_path, num_seeds=NUM_SEEDS)
        elapsed = round(time.time() - t0, 1)

        results[problem] = brit

        if brit["is_brittle"]:
            brittle.append(problem)
            print(f"BRITTLE ({brit['passes']}/{brit['total_seeds']} seeds) [{elapsed}s]")
        elif brit["always_fails"]:
            always_fail.append(problem)
            print(f"ALWAYS FAILS (0/{brit['total_seeds']} seeds) [{elapsed}s]")
        else:
            stable.append(problem)
            print(f"STABLE ({brit['passes']}/{brit['total_seeds']}) [{elapsed}s]")

    # Summary
    print(f"\n{'='*60}")
    print(f"BRITTLENESS SUMMARY")
    print(f"{'='*60}")
    print(f"Total:        {len(results)}")
    print(f"Stable:       {len(stable)}")
    print(f"Brittle:      {len(brittle)}")
    print(f"Always fails: {len(always_fail)}")

    if brittle:
        print(f"\nBrittle programs:")
        for p in brittle:
            b = results[p]
            print(f"  {p}: {b['passes']}/{b['total_seeds']} seeds pass")

    if always_fail:
        print(f"\nAlways-fail programs:")
        for p in always_fail:
            print(f"  {p}")

    # Save results
    output_path = SCRIPT_DIR / "brittleness_results.json"
    output_path.write_text(json.dumps({
        "num_seeds": NUM_SEEDS,
        "timeout": VERIFY_TIMEOUT,
        "total": len(results),
        "stable_count": len(stable),
        "brittle_count": len(brittle),
        "always_fail_count": len(always_fail),
        "stable": stable,
        "brittle": brittle,
        "always_fail": always_fail,
        "per_problem": results,
    }, indent=2))
    print(f"\nSaved to {output_path}")


if __name__ == "__main__":
    main()
