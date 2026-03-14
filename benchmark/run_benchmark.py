#!/usr/bin/env python3
"""
Benchmark runner for evaluating LLMs on Dafny verification tasks.

Usage:
    python run_benchmark.py --dataset ./dataset/problems --llm claude-code --timeout 600 --max-iterations 20

The runner:
  1. Reads all problems from the dataset directory
  2. For each problem, sets up the proxy environment and launches the LLM
  3. Collects results (success/fail, iterations, time, solution)
  4. Outputs JSON results + markdown summary
"""

import argparse
import json
import os
import shutil
import sys
import tempfile
import time
from datetime import datetime
from pathlib import Path
from typing import List, Optional

# Add parent to path for imports
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from adapters.base_adapter import BaseAdapter, Result
from adapters.claude_code import ClaudeCodeAdapter
from adapters.manual import ManualAdapter


DEFAULT_REAL_DAFNY = "/opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll"

PROXY_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "dafny-proxy")


def get_adapter(llm_name: str, model: str = "") -> BaseAdapter:
    """Factory function to create an adapter by name."""
    adapters = {
        "claude-code": lambda: ClaudeCodeAdapter(model=model),
        "manual": lambda: ManualAdapter(),
    }
    if llm_name not in adapters:
        raise ValueError(
            f"Unknown LLM adapter: {llm_name}. Available: {list(adapters.keys())}"
        )
    return adapters[llm_name]()


def discover_problems(dataset_dir: str) -> List[dict]:
    """
    Discover all problems in the dataset directory.

    Each problem is a subdirectory containing at least `task.dfy`.
    Optionally contains `description.txt` and `solution.dfy`.
    """
    problems = []
    dataset_path = Path(dataset_dir)

    if not dataset_path.exists():
        print(f"ERROR: Dataset directory does not exist: {dataset_dir}", file=sys.stderr)
        sys.exit(1)

    for entry in sorted(dataset_path.iterdir()):
        if not entry.is_dir():
            continue
        task_file = entry / "task.dfy"
        if not task_file.exists():
            continue

        problem = {
            "name": entry.name,
            "dir": str(entry),
            "task_file": str(task_file),
        }

        desc_file = entry / "description.txt"
        if desc_file.exists():
            problem["description"] = desc_file.read_text().strip()

        solution_file = entry / "solution.dfy"
        if solution_file.exists():
            problem["solution_file"] = str(solution_file)

        problems.append(problem)

    return problems


def run_single_problem(
    problem: dict,
    adapter: BaseAdapter,
    timeout: int,
    max_iterations: int,
    real_dafny: str,
    output_dir: str,
) -> dict:
    """
    Run a single problem through the LLM adapter.

    Sets up the proxy environment, copies the task file, launches the adapter,
    and collects results.
    """
    problem_name = problem["name"]
    print(f"\n{'='*60}")
    print(f"Problem: {problem_name}")
    print(f"{'='*60}")

    # Create working directory
    work_dir = os.path.join(output_dir, problem_name, "workspace")
    os.makedirs(work_dir, exist_ok=True)

    # Copy task file to working directory
    task_copy = os.path.join(work_dir, "task.dfy")
    shutil.copy2(problem["task_file"], task_copy)

    # Set up log file
    log_file = os.path.join(output_dir, problem_name, "proxy.log")

    # Build environment
    env = {
        "BENCHMARK_TASK_FILE": os.path.abspath(problem["task_file"]),
        "BENCHMARK_REAL_DAFNY": real_dafny,
        "BENCHMARK_LOG_FILE": log_file,
        "BENCHMARK_PROXY_DIR": PROXY_DIR,
        "BENCHMARK_MAX_ITERATIONS": str(max_iterations),
        "BENCHMARK_TIMEOUT": str(timeout),
        # Put the proxy first on PATH
        "PATH": PROXY_DIR + ":" + os.environ.get("PATH", ""),
    }

    print(f"  Working dir: {work_dir}")
    print(f"  Log file:    {log_file}")
    print(f"  Timeout:     {timeout}s")
    print(f"  Max iters:   {max_iterations}")

    start_time = time.time()

    # Run the adapter
    result = adapter.run(
        problem_dir=problem["dir"],
        working_dir=work_dir,
        timeout=timeout,
        max_iterations=max_iterations,
        env=env,
    )

    elapsed = time.time() - start_time

    # Copy the solution file if it exists
    if result.solution_path and os.path.exists(result.solution_path):
        solution_copy = os.path.join(output_dir, problem_name, "solution.dfy")
        shutil.copy2(result.solution_path, solution_copy)
        result.solution_path = solution_copy

    # Print summary
    status = "PASS" if result.success else "FAIL"
    if result.timed_out:
        status = "TIMEOUT"
    elif result.max_iterations_reached:
        status = "MAX_ITER"

    print(f"\n  Result: {status}")
    print(f"  Iterations: {result.iterations}")
    print(f"  Time: {result.time_seconds:.1f}s")
    if result.error:
        print(f"  Error: {result.error}")

    return {
        "problem": problem_name,
        "result": result.to_dict(),
        "status": status,
    }


def generate_markdown_summary(results: List[dict], adapter_name: str) -> str:
    """Generate a markdown summary table from results."""
    lines = []
    lines.append(f"# Benchmark Results: {adapter_name}")
    lines.append(f"\nRun at: {datetime.now().isoformat()}")
    lines.append("")
    lines.append("| Problem | Status | Iterations | Time (s) |")
    lines.append("|---------|--------|------------|----------|")

    total_success = 0
    total_problems = len(results)
    total_time = 0.0
    total_iterations = 0

    for r in results:
        status = r["status"]
        iters = r["result"]["iterations"]
        time_s = r["result"]["time_seconds"]
        total_time += time_s
        total_iterations += iters
        if r["result"]["success"]:
            total_success += 1

        lines.append(f"| {r['problem']} | {status} | {iters} | {time_s:.1f} |")

    lines.append("")
    lines.append(f"**Total:** {total_success}/{total_problems} solved")
    lines.append(f"**Average time:** {total_time/max(total_problems,1):.1f}s")
    lines.append(f"**Average iterations:** {total_iterations/max(total_problems,1):.1f}")
    lines.append("")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Run Dafny verification benchmark on LLMs"
    )
    parser.add_argument(
        "--dataset",
        required=True,
        help="Path to dataset directory containing problem subdirectories",
    )
    parser.add_argument(
        "--llm",
        required=True,
        choices=["claude-code", "manual"],
        help="LLM adapter to use",
    )
    parser.add_argument(
        "--model",
        default="",
        help="Model identifier to pass to the LLM (adapter-specific)",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=600,
        help="Timeout per problem in seconds (default: 600)",
    )
    parser.add_argument(
        "--max-iterations",
        type=int,
        default=20,
        help="Maximum dafny verify calls per problem (default: 20)",
    )
    parser.add_argument(
        "--real-dafny",
        default=DEFAULT_REAL_DAFNY,
        help="Command to run the real dafny",
    )
    parser.add_argument(
        "--output-dir",
        default=None,
        help="Output directory for results (default: auto-generated)",
    )
    parser.add_argument(
        "--problems",
        nargs="*",
        default=None,
        help="Specific problem names to run (default: all)",
    )

    args = parser.parse_args()

    # Create output directory
    if args.output_dir:
        output_dir = args.output_dir
    else:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        output_dir = os.path.join(
            os.path.dirname(os.path.abspath(__file__)),
            "results",
            f"{args.llm}_{timestamp}",
        )

    os.makedirs(output_dir, exist_ok=True)
    print(f"Output directory: {output_dir}")

    # Discover problems
    problems = discover_problems(args.dataset)
    if not problems:
        print("ERROR: No problems found in dataset directory", file=sys.stderr)
        sys.exit(1)

    # Filter problems if specified
    if args.problems:
        problems = [p for p in problems if p["name"] in args.problems]
        if not problems:
            print(
                f"ERROR: None of the specified problems found: {args.problems}",
                file=sys.stderr,
            )
            sys.exit(1)

    print(f"Found {len(problems)} problems: {[p['name'] for p in problems]}")

    # Create adapter
    adapter = get_adapter(args.llm, model=args.model)
    print(f"Using adapter: {adapter.name}")

    # Verify proxy exists
    proxy_path = os.path.join(PROXY_DIR, "dafny")
    if not os.path.exists(proxy_path):
        print(f"ERROR: Proxy not found at {proxy_path}", file=sys.stderr)
        sys.exit(1)

    # Run each problem
    all_results = []
    for problem in problems:
        result = run_single_problem(
            problem=problem,
            adapter=adapter,
            timeout=args.timeout,
            max_iterations=args.max_iterations,
            real_dafny=args.real_dafny,
            output_dir=output_dir,
        )
        all_results.append(result)

    # Save JSON results
    results_file = os.path.join(output_dir, "results.json")
    with open(results_file, "w") as f:
        json.dump(
            {
                "adapter": adapter.name,
                "model": args.model,
                "timeout": args.timeout,
                "max_iterations": args.max_iterations,
                "timestamp": datetime.now().isoformat(),
                "results": all_results,
            },
            f,
            indent=2,
        )
    print(f"\nResults saved to: {results_file}")

    # Generate and save markdown summary
    summary = generate_markdown_summary(all_results, adapter.name)
    summary_file = os.path.join(output_dir, "summary.md")
    with open(summary_file, "w") as f:
        f.write(summary)
    print(f"Summary saved to: {summary_file}")

    # Print summary to stdout
    print("\n" + summary)

    # Exit with non-zero if any problem failed
    all_passed = all(r["result"]["success"] for r in all_results)
    sys.exit(0 if all_passed else 1)


if __name__ == "__main__":
    main()
