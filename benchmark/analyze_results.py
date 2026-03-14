#!/usr/bin/env python3
"""
Analyze benchmark results from multiple runs.

Reads JSON results files and produces:
  - LLM x Problem comparison matrix
  - verify@k metrics (for k=5, 10, 20)
  - Average time per problem
  - Markdown report

Usage:
    python analyze_results.py results/run1/results.json results/run2/results.json ...
    python analyze_results.py results/  # scan all results.json recursively
"""

import argparse
import json
import os
import sys
from collections import defaultdict
from pathlib import Path
from typing import List, Dict, Optional


def load_results(paths: List[str]) -> List[dict]:
    """Load results from one or more paths (files or directories)."""
    results_files = []

    for p in paths:
        path = Path(p)
        if path.is_file() and path.name == "results.json":
            results_files.append(path)
        elif path.is_dir():
            # Recursively find results.json files
            for rfile in sorted(path.rglob("results.json")):
                results_files.append(rfile)
        else:
            print(f"WARNING: Skipping {p} (not a results.json file or directory)",
                  file=sys.stderr)

    all_runs = []
    for rf in results_files:
        try:
            with open(rf, 'r') as f:
                data = json.load(f)
            data['_source_file'] = str(rf)
            all_runs.append(data)
            print(f"Loaded: {rf}")
        except (json.JSONDecodeError, FileNotFoundError) as e:
            print(f"WARNING: Could not load {rf}: {e}", file=sys.stderr)

    return all_runs


def compute_verify_at_k(runs: List[dict], k: int) -> Dict[str, float]:
    """
    Compute verify@k: for each problem, what fraction of runs solved it
    within k iterations?

    Returns dict mapping problem name to success rate.
    """
    problem_results = defaultdict(list)

    for run in runs:
        for r in run.get('results', []):
            problem = r['problem']
            success = r['result']['success']
            iterations = r['result']['iterations']
            # verify@k: succeeded within k iterations
            solved_at_k = success and iterations <= k
            problem_results[problem].append(solved_at_k)

    rates = {}
    for problem, outcomes in problem_results.items():
        rates[problem] = sum(outcomes) / len(outcomes) if outcomes else 0.0

    return rates


def build_comparison_matrix(runs: List[dict]) -> dict:
    """
    Build an LLM x Problem comparison matrix.

    Returns:
        {
            'llms': [list of LLM names],
            'problems': [list of problem names],
            'matrix': {llm: {problem: {success, iterations, time}}}
        }
    """
    llms = set()
    problems = set()
    matrix = defaultdict(dict)

    for run in runs:
        adapter = run.get('adapter', 'unknown')
        model = run.get('model', '')
        llm_name = f"{adapter}" + (f" ({model})" if model else "")
        llms.add(llm_name)

        for r in run.get('results', []):
            problem = r['problem']
            problems.add(problem)
            matrix[llm_name][problem] = {
                'success': r['result']['success'],
                'iterations': r['result']['iterations'],
                'time_seconds': r['result']['time_seconds'],
                'status': r.get('status', 'UNKNOWN'),
            }

    return {
        'llms': sorted(llms),
        'problems': sorted(problems),
        'matrix': dict(matrix),
    }


def generate_report(runs: List[dict], output_path: Optional[str] = None) -> str:
    """Generate a comprehensive markdown report."""
    lines = []
    lines.append("# Dafny Verification Benchmark Report")
    lines.append("")

    if not runs:
        lines.append("No results to analyze.")
        return "\n".join(lines)

    # Overview
    lines.append("## Overview")
    lines.append("")
    lines.append(f"Total runs analyzed: {len(runs)}")
    lines.append("")

    for run in runs:
        adapter = run.get('adapter', 'unknown')
        model = run.get('model', '')
        timestamp = run.get('timestamp', 'unknown')
        n_problems = len(run.get('results', []))
        n_solved = sum(1 for r in run.get('results', []) if r['result']['success'])
        lines.append(f"- **{adapter}** {model}: {n_solved}/{n_problems} solved (run: {timestamp})")

    lines.append("")

    # Comparison matrix
    comp = build_comparison_matrix(runs)
    if len(comp['llms']) > 0:
        lines.append("## Comparison Matrix")
        lines.append("")

        # Header
        header = "| Problem |"
        separator = "|---------|"
        for llm in comp['llms']:
            header += f" {llm} |"
            separator += "------|"
        lines.append(header)
        lines.append(separator)

        # Rows
        for problem in comp['problems']:
            row = f"| {problem} |"
            for llm in comp['llms']:
                cell = comp['matrix'].get(llm, {}).get(problem, None)
                if cell:
                    status = cell['status']
                    iters = cell['iterations']
                    time_s = cell['time_seconds']
                    if cell['success']:
                        row += f" PASS ({iters}i, {time_s:.0f}s) |"
                    else:
                        row += f" {status} ({iters}i, {time_s:.0f}s) |"
                else:
                    row += " - |"
            lines.append(row)

        lines.append("")

    # Verify@k metrics
    lines.append("## Verify@k Metrics")
    lines.append("")
    lines.append("Success rate when limiting to k iterations:")
    lines.append("")

    k_values = [5, 10, 20]
    header = "| Problem |"
    separator = "|---------|"
    for k in k_values:
        header += f" @{k} |"
        separator += "------|"
    lines.append(header)
    lines.append(separator)

    all_problems = set()
    for run in runs:
        for r in run.get('results', []):
            all_problems.add(r['problem'])

    for problem in sorted(all_problems):
        row = f"| {problem} |"
        for k in k_values:
            rates = compute_verify_at_k(runs, k)
            rate = rates.get(problem, 0.0)
            row += f" {rate*100:.0f}% |"
        lines.append(row)

    # Overall verify@k
    lines.append("")
    lines.append("**Overall:**")
    lines.append("")
    for k in k_values:
        rates = compute_verify_at_k(runs, k)
        if rates:
            overall = sum(rates.values()) / len(rates)
            lines.append(f"- verify@{k}: {overall*100:.1f}%")

    lines.append("")

    # Per-LLM statistics
    lines.append("## Per-LLM Statistics")
    lines.append("")

    for run in runs:
        adapter = run.get('adapter', 'unknown')
        model = run.get('model', '')
        llm_name = f"{adapter}" + (f" ({model})" if model else "")
        results = run.get('results', [])

        if not results:
            continue

        n_problems = len(results)
        n_solved = sum(1 for r in results if r['result']['success'])
        total_time = sum(r['result']['time_seconds'] for r in results)
        total_iters = sum(r['result']['iterations'] for r in results)
        solved_times = [r['result']['time_seconds'] for r in results if r['result']['success']]
        solved_iters = [r['result']['iterations'] for r in results if r['result']['success']]

        lines.append(f"### {llm_name}")
        lines.append("")
        lines.append(f"- Problems solved: {n_solved}/{n_problems} ({n_solved/n_problems*100:.0f}%)")
        lines.append(f"- Total time: {total_time:.0f}s")
        lines.append(f"- Average time per problem: {total_time/n_problems:.0f}s")
        if solved_times:
            lines.append(f"- Average time (solved only): {sum(solved_times)/len(solved_times):.0f}s")
            lines.append(f"- Average iterations (solved only): {sum(solved_iters)/len(solved_iters):.1f}")
        lines.append("")

    report = "\n".join(lines)

    if output_path:
        with open(output_path, 'w') as f:
            f.write(report)
        print(f"Report saved to: {output_path}")

    return report


def main():
    parser = argparse.ArgumentParser(
        description="Analyze Dafny verification benchmark results"
    )
    parser.add_argument(
        "paths",
        nargs="+",
        help="Paths to results.json files or directories containing them",
    )
    parser.add_argument(
        "--output",
        "-o",
        default=None,
        help="Output path for the markdown report",
    )
    parser.add_argument(
        "--json",
        default=None,
        dest="json_output",
        help="Output path for structured JSON analysis",
    )

    args = parser.parse_args()

    runs = load_results(args.paths)
    if not runs:
        print("ERROR: No results files found", file=sys.stderr)
        sys.exit(1)

    report = generate_report(runs, args.output)
    print("\n" + report)

    if args.json_output:
        comp = build_comparison_matrix(runs)
        k_metrics = {}
        for k in [5, 10, 20]:
            k_metrics[f"verify@{k}"] = compute_verify_at_k(runs, k)

        analysis = {
            "comparison_matrix": comp,
            "verify_at_k": k_metrics,
            "runs": [
                {
                    "adapter": r.get('adapter'),
                    "model": r.get('model'),
                    "timestamp": r.get('timestamp'),
                    "source": r.get('_source_file'),
                    "num_problems": len(r.get('results', [])),
                    "num_solved": sum(1 for x in r.get('results', []) if x['result']['success']),
                }
                for r in runs
            ],
        }

        with open(args.json_output, 'w') as f:
            json.dump(analysis, f, indent=2)
        print(f"\nJSON analysis saved to: {args.json_output}")


if __name__ == "__main__":
    main()
