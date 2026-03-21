#!/usr/bin/env python3
from __future__ import annotations
"""
Aggregate results from multiple benchmark runs for the same model.

Computes mean, std, and confidence intervals for pass rate, per-problem
success probability, and attempt counts.

Usage:
    # Aggregate all runs for a model (finds dirs by pattern)
    python3 aggregate_runs.py --model kimi-dev-72b --mode full

    # Aggregate specific directories
    python3 aggregate_runs.py --dirs results/run1 results/run2 results/run3

    # Aggregate from Leonardo (reads from remote)
    python3 aggregate_runs.py --model kimi-dev-72b --mode full --remote
"""

import argparse
import json
import math
import os
import sys
from collections import Counter, defaultdict
from pathlib import Path

RESULTS_BASE = Path(__file__).parent / "results"


def _load_single_dir(results_dir: Path) -> dict:
    """Load results from a single directory."""
    problems = {}
    for d in sorted(results_dir.iterdir()):
        rp = d / "result.json"
        if not rp.exists():
            continue
        r = json.loads(rp.read_text())
        problems[d.name] = {
            "success": r.get("success", False),
            "attempts": r.get("total_attempts", 0),
            "time": r.get("total_time", 0),
            "tokens": r.get("total_tokens", 0),
        }
    return problems


def find_runs(model: str, mode: str, base: Path = RESULTS_BASE,
              exp_id: str | None = None) -> list:
    """Find result directories for a model/mode experiment.

    Groups by exp-id (the trailing YYYYMMDD_HHMMSS in the dir name).
    If --exp-id not specified, picks the latest exp-id.
    Within an exp-id, groups by run-id and merges batches.

    Returns list of entries, each either a Path or list[Path] (batched run).
    """
    import re

    pattern = f"results_{mode}_{model}"
    all_dirs = sorted([d for d in base.iterdir() if d.is_dir() and d.name.startswith(pattern)])

    # Parse each directory
    parsed = []  # (dir, run_id, batch_id, exp_id_str)
    for d in all_dirs:
        name = d.name
        run_match = re.search(r'_run(\d+)', name)
        if not run_match:
            continue
        run_id = run_match.group(1)

        batch_match = re.search(r'_batch(\d+)', name)
        batch_id = batch_match.group(1) if batch_match else None

        ts_match = re.search(r'_(\d{8}_\d{6})$', name)
        exp_ts = ts_match.group(1) if ts_match else ""

        parsed.append((d, run_id, batch_id, exp_ts))

    if not parsed:
        return []

    # Find the target exp-id
    if exp_id:
        # Exact match
        filtered = [(d, run_id, batch_id) for d, run_id, batch_id, exp_ts in parsed
                    if exp_ts == exp_id]
    else:
        # Group timestamps within 120s as same experiment
        from datetime import datetime
        def parse_ts(ts):
            try:
                return datetime.strptime(ts, "%Y%m%d_%H%M%S")
            except ValueError:
                return None

        # Sort by timestamp descending (latest first)
        with_dt = [(d, run_id, batch_id, exp_ts, parse_ts(exp_ts)) for d, run_id, batch_id, exp_ts in parsed]
        with_dt = [(d, r, b, ts, dt) for d, r, b, ts, dt in with_dt if dt is not None]
        with_dt.sort(key=lambda x: x[4], reverse=True)

        if not with_dt:
            return []

        # Start from latest timestamp, include all within 120s window
        latest_dt = with_dt[0][4]
        filtered = [(d, run_id, batch_id) for d, run_id, batch_id, ts, dt in with_dt
                    if abs((dt - latest_dt).total_seconds()) <= 120]

    # Group by run-id, merging batches
    by_run = {}
    for d, run_id, batch_id in filtered:
        by_run.setdefault(run_id, []).append(d)

    result = []
    for run_id in sorted(by_run.keys()):
        dirs = by_run[run_id]
        if len(dirs) == 1:
            result.append(dirs[0])
        else:
            result.append(dirs)

    return result


def load_run(results_input) -> dict:
    """Load results from one run. Input can be a single Path or list of Paths (batched)."""
    if isinstance(results_input, list):
        # Batched run — merge all batch dirs
        problems = {}
        for d in results_input:
            problems.update(_load_single_dir(d))
        return problems
    else:
        return _load_single_dir(results_input)


def mean(values: list) -> float:
    return sum(values) / len(values) if values else 0


def std(values: list) -> float:
    if len(values) < 2:
        return 0
    m = mean(values)
    return math.sqrt(sum((v - m) ** 2 for v in values) / (len(values) - 1))


def ci95(values: list) -> tuple[float, float]:
    """95% confidence interval (t-distribution approximation)."""
    n = len(values)
    if n < 2:
        return (mean(values), mean(values))
    m = mean(values)
    s = std(values)
    # t-value for 95% CI (approximation for small n)
    t = {2: 12.71, 3: 4.30, 4: 3.18, 5: 2.78, 6: 2.57, 7: 2.45,
         8: 2.36, 9: 2.31, 10: 2.26}.get(n, 1.96)
    margin = t * s / math.sqrt(n)
    return (m - margin, m + margin)


def aggregate(runs: list[dict]) -> dict:
    """Aggregate results from multiple runs."""
    n_runs = len(runs)

    # All problem names (union across runs)
    all_problems = sorted(set().union(*(r.keys() for r in runs)))

    # Per-problem stats
    per_problem = {}
    for prob in all_problems:
        successes = [r[prob]["success"] for r in runs if prob in r]
        attempts = [r[prob]["attempts"] for r in runs if prob in r]
        times = [r[prob]["time"] for r in runs if prob in r]

        n_success = sum(successes)
        n_total = len(successes)
        rate = n_success / n_total if n_total else 0

        per_problem[prob] = {
            "n_runs": n_total,
            "n_success": n_success,
            "success_rate": round(rate, 3),
            "always_pass": rate == 1.0,
            "always_fail": rate == 0.0,
            "flaky": 0 < rate < 1,
            "attempts_mean": round(mean(attempts), 1),
            "attempts_std": round(std(attempts), 1),
            "time_mean": round(mean(times), 0),
        }

    # Overall stats per run
    pass_counts = [sum(1 for p in r.values() if p["success"]) for r in runs]
    total_per_run = [len(r) for r in runs]
    pass_rates = [p / t if t else 0 for p, t in zip(pass_counts, total_per_run)]

    # Classify problems
    always_pass = [p for p, s in per_problem.items() if s["always_pass"]]
    always_fail = [p for p, s in per_problem.items() if s["always_fail"]]
    flaky = [p for p, s in per_problem.items() if s["flaky"]]

    report = {
        "n_runs": n_runs,
        "n_problems": len(all_problems),
        "pass_rate": {
            "mean": round(mean(pass_rates) * 100, 1),
            "std": round(std(pass_rates) * 100, 1),
            "ci95": tuple(round(x * 100, 1) for x in ci95(pass_rates)),
            "per_run": [round(r * 100, 1) for r in pass_rates],
            "pass_counts": pass_counts,
        },
        "problems": {
            "always_pass": len(always_pass),
            "always_fail": len(always_fail),
            "flaky": len(flaky),
            "always_pass_list": always_pass,
            "always_fail_list": always_fail,
            "flaky_list": flaky,
        },
        "per_problem": per_problem,
    }

    return report


def print_report(report: dict, model: str = ""):
    """Print human-readable report."""
    print(f"\n{'='*60}")
    print(f"Aggregated Results{f' — {model}' if model else ''}")
    print(f"{'='*60}")
    print(f"Runs: {report['n_runs']}")
    print(f"Problems: {report['n_problems']}")

    pr = report["pass_rate"]
    print(f"\nPass rate: {pr['mean']}% ± {pr['std']}%")
    print(f"  95% CI: [{pr['ci95'][0]}%, {pr['ci95'][1]}%]")
    print(f"  Per run: {pr['per_run']}")
    print(f"  Pass counts: {pr['pass_counts']}")

    probs = report["problems"]
    print(f"\nProblem stability:")
    print(f"  Always pass:  {probs['always_pass']} problems")
    print(f"  Always fail:  {probs['always_fail']} problems")
    print(f"  Flaky:        {probs['flaky']} problems")

    if probs["flaky_list"]:
        print(f"\nFlaky problems (pass in some runs, fail in others):")
        for p in probs["flaky_list"]:
            s = report["per_problem"][p]
            print(f"  {p}: {s['n_success']}/{s['n_runs']} pass ({s['success_rate']*100:.0f}%)")


def main():
    parser = argparse.ArgumentParser(description="Aggregate multiple benchmark runs")
    parser.add_argument("--model", help="Model name to find runs for")
    parser.add_argument("--mode", default="full", help="Benchmark mode (full/placeholder)")
    parser.add_argument("--exp-id", default=None, help="Specific experiment ID (default: latest)")
    parser.add_argument("--dirs", nargs="+", help="Explicit result directories")
    parser.add_argument("--base", default=None, help="Base directory to search")
    parser.add_argument("--output", help="Output JSON path")
    args = parser.parse_args()

    if args.dirs:
        run_dirs = [Path(d) for d in args.dirs]
    elif args.model:
        base = Path(args.base) if args.base else RESULTS_BASE
        run_dirs = find_runs(args.model, args.mode, base, args.exp_id)
    else:
        print("ERROR: specify --model or --dirs")
        sys.exit(1)

    if not run_dirs:
        print(f"No runs found")
        sys.exit(1)

    print(f"Found {len(run_dirs)} runs:")
    for d in run_dirs:
        if isinstance(d, list):
            print(f"  batched ({len(d)} dirs): {d[0].name} ...")
        else:
            print(f"  {d.name}")

    runs = []
    for d in run_dirs:
        r = load_run(d)
        if r:
            runs.append(r)
            label = d[0].name if isinstance(d, list) else d.name
            print(f"  {label}: {len(r)} problems, {sum(1 for v in r.values() if v['success'])} pass")

    if len(runs) < 2:
        print(f"\nNeed at least 2 runs to aggregate (found {len(runs)})")
        if runs:
            print("Single run results:")
            r = runs[0]
            s = sum(1 for v in r.values() if v["success"])
            print(f"  {s}/{len(r)} pass ({100*s/len(r):.1f}%)")
        sys.exit(0)

    report = aggregate(runs)
    print_report(report, args.model or "")

    if args.output:
        Path(args.output).write_text(json.dumps(report, indent=2))
        print(f"\nSaved to: {args.output}")


if __name__ == "__main__":
    main()
