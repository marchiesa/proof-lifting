#!/usr/bin/env python3
"""
Benchmark runner for evaluating LLMs on Dafny verification tasks.

Usage (original, still works):
    python run_benchmark.py --dataset ./dataset/problems --llm claude-code --timeout 600 --max-iterations 20

New adapter/parallel flags:
    python run_benchmark.py --dataset ./dataset/problems \\
        --adapter openai_compatible --base-url http://localhost:8000/v1 \\
        --model meta-llama/Llama-3.1-70B-Instruct --parallel 4

Config-file driven:
    python run_benchmark.py --config config.yaml

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
import subprocess
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


# ── Adapter name aliases ─────────────────────────────────────────────
# Supports both dashed (legacy) and underscored (new) forms.
_ADAPTER_ALIASES = {
    "claude-code": "claude_code",
    "claude_code": "claude_code",
    "manual": "manual",
    "openai_compatible": "openai_compatible",
    "openai-compatible": "openai_compatible",
    "hf_transformers": "hf_transformers",
    "hf-transformers": "hf_transformers",
}


def get_adapter(
    llm_name: str,
    *,
    model: str = "",
    base_url: Optional[str] = None,
    api_key: Optional[str] = None,
    model_path: Optional[str] = None,
    device: str = "auto",
) -> BaseAdapter:
    """
    Factory function to create an adapter by name.

    Parameters
    ----------
    llm_name : str
        Adapter identifier (see ``_ADAPTER_ALIASES``).
    model : str
        Model identifier (meaning is adapter-specific).
    base_url : str, optional
        API base URL (openai_compatible adapter).
    api_key : str, optional
        API key (openai_compatible adapter).
    model_path : str, optional
        Local model path (hf_transformers adapter).
    device : str
        Device string (hf_transformers adapter).
    """
    canonical = _ADAPTER_ALIASES.get(llm_name)
    if canonical is None:
        raise ValueError(
            f"Unknown LLM adapter: {llm_name}. "
            f"Available: {sorted(set(_ADAPTER_ALIASES.values()))}"
        )

    if canonical == "claude_code":
        return ClaudeCodeAdapter(model=model)

    if canonical == "manual":
        return ManualAdapter()

    if canonical == "openai_compatible":
        from adapters.openai_compatible import OpenAICompatibleAdapter

        kwargs = {"model_name": model}
        if base_url:
            kwargs["base_url"] = base_url
        if api_key:
            kwargs["api_key"] = api_key
        return OpenAICompatibleAdapter(**kwargs)

    if canonical == "hf_transformers":
        from adapters.hf_transformers import HFTransformersAdapter

        kwargs = {}
        if model_path:
            kwargs["model_path"] = model_path
        elif model:
            kwargs["model_path"] = model
        if device:
            kwargs["device"] = device
        return HFTransformersAdapter(**kwargs)

    raise ValueError(f"Unhandled adapter: {canonical}")


def run_tests(problem_dir: str, real_dafny: str) -> tuple:
    """
    Run runtime tests (spec + implementation) for a problem.

    Looks for ``tests.dfy`` in the problem directory and executes it with
    ``dafny run``. Returns ``(passed: bool, output: str)``.
    """
    tests_file = os.path.join(problem_dir, "tests.dfy")
    if not os.path.exists(tests_file):
        return False, "tests.dfy not found"

    # Build the dafny run command
    dafny_parts = real_dafny.split()
    cmd = dafny_parts + ["run", tests_file]

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=120,
        )
        output = result.stdout + result.stderr
        passed = result.returncode == 0
        return passed, output.strip()
    except subprocess.TimeoutExpired:
        return False, "Tests timed out after 120s"
    except Exception as e:
        return False, f"Error running tests: {e}"


def discover_problems(dataset_dir: str) -> List[dict]:
    """
    Discover all problems in the dataset directory.

    Each problem is a subdirectory containing at least ``task.dfy``.
    Optionally contains ``description.txt`` and ``solution.dfy``.
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
    skip_tests: bool = False,
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

    # Run tests if verification passed and not skipped
    test_passed = None
    test_output = None
    if result.success and not skip_tests:
        tests_file = os.path.join(problem["dir"], "tests.dfy")
        if os.path.exists(tests_file):
            print("  Running tests...")
            test_passed, test_output = run_tests(
                problem["dir"], real_dafny
            )
            if not test_passed:
                status = "TEST_FAIL"
                print(f"  Tests: FAILED")
                print(f"  Test output: {test_output}")
            else:
                print(f"  Tests: PASSED")

    print(f"\n  Result: {status}")
    print(f"  Iterations: {result.iterations}")
    print(f"  Time: {result.time_seconds:.1f}s")
    if result.error:
        print(f"  Error: {result.error}")

    result_dict = result.to_dict()
    if test_passed is not None:
        result_dict["test_passed"] = test_passed
        result_dict["test_output"] = test_output

    return {
        "problem": problem_name,
        "result": result_dict,
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


# ── Config-file support ──────────────────────────────────────────────


def _load_config(path: str) -> dict:
    """Load a YAML config file, falling back to JSON."""
    try:
        import yaml  # type: ignore[import-untyped]

        with open(path, "r") as f:
            return yaml.safe_load(f)
    except ImportError:
        with open(path, "r") as f:
            return json.load(f)


def main():
    parser = argparse.ArgumentParser(
        description="Run Dafny verification benchmark on LLMs"
    )
    parser.add_argument(
        "--config",
        default=None,
        help="Path to YAML/JSON config file (overrides other flags)",
    )
    parser.add_argument(
        "--dataset",
        default=None,
        help="Path to dataset directory containing problem subdirectories",
    )
    # Legacy flag (kept for backward compatibility).
    parser.add_argument(
        "--llm",
        default=None,
        help="LLM adapter to use (legacy; prefer --adapter)",
    )
    parser.add_argument(
        "--adapter",
        default=None,
        choices=["claude_code", "manual", "openai_compatible", "hf_transformers"],
        help="Adapter name",
    )
    parser.add_argument(
        "--model",
        default="",
        help="Model identifier to pass to the LLM (adapter-specific)",
    )
    parser.add_argument(
        "--base-url",
        default=None,
        help="API base URL for openai_compatible adapter",
    )
    parser.add_argument(
        "--api-key",
        default=None,
        help="API key for openai_compatible adapter",
    )
    parser.add_argument(
        "--model-path",
        default=None,
        help="Local model path for hf_transformers adapter",
    )
    parser.add_argument(
        "--device",
        default="auto",
        help="Device for hf_transformers adapter (default: auto)",
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
    parser.add_argument(
        "--parallel",
        type=int,
        default=None,
        metavar="N",
        help="Run problems in parallel with N workers (uses parallel_runner)",
    )
    parser.add_argument(
        "--skip-tests",
        "--skip-spec-tests",
        action="store_true",
        default=False,
        dest="skip_tests",
        help="Skip runtime tests (spec + implementation) after successful verification",
    )

    args = parser.parse_args()

    # ── Merge config if provided ─────────────────────────────────────
    cfg: dict = {}
    if args.config:
        cfg = _load_config(args.config)

    # Resolve values: CLI > config > defaults.
    dataset = args.dataset or cfg.get("problems_dir") or cfg.get("dataset")
    adapter_name = args.adapter or args.llm or cfg.get("adapter")
    model = args.model or cfg.get("model", "")
    base_url = args.base_url or cfg.get("base_url")
    api_key = args.api_key or cfg.get("api_key")
    model_path = args.model_path or cfg.get("model_path")
    device = args.device if args.device != "auto" else cfg.get("device", "auto")
    timeout_val = args.timeout if args.timeout != 600 else cfg.get("timeout", 600)
    max_iters = (
        args.max_iterations
        if args.max_iterations != 20
        else cfg.get("max_iterations", 20)
    )
    real_dafny = (
        args.real_dafny
        if args.real_dafny != DEFAULT_REAL_DAFNY
        else cfg.get("dafny_path", DEFAULT_REAL_DAFNY)
    )
    output_dir_arg = args.output_dir or cfg.get("output_dir")
    parallel = args.parallel or cfg.get("parallel_workers")
    problem_names = args.problems or cfg.get("problems")
    skip_tests = args.skip_tests or cfg.get("skip_tests", cfg.get("skip_spec_tests", False))

    if not dataset:
        parser.error("--dataset is required (or set problems_dir in config)")
    if not adapter_name:
        parser.error("--llm or --adapter is required (or set adapter in config)")

    # ── Create output directory ──────────────────────────────────────
    if output_dir_arg:
        output_dir = output_dir_arg
    else:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        display_name = _ADAPTER_ALIASES.get(adapter_name, adapter_name)
        output_dir = os.path.join(
            os.path.dirname(os.path.abspath(__file__)),
            "results",
            f"{display_name}_{timestamp}",
        )

    os.makedirs(output_dir, exist_ok=True)
    print(f"Output directory: {output_dir}")

    # ── Discover problems ────────────────────────────────────────────
    problems = discover_problems(dataset)
    if not problems:
        print("ERROR: No problems found in dataset directory", file=sys.stderr)
        sys.exit(1)

    if problem_names:
        problems = [p for p in problems if p["name"] in problem_names]
        if not problems:
            print(
                f"ERROR: None of the specified problems found: {problem_names}",
                file=sys.stderr,
            )
            sys.exit(1)

    print(f"Found {len(problems)} problems: {[p['name'] for p in problems]}")

    # ── Parallel mode ────────────────────────────────────────────────
    if parallel and parallel > 1:
        from parallel_runner import run_parallel, save_json, save_csv

        adapter_kwargs = {"model": model}
        if base_url:
            adapter_kwargs["base_url"] = base_url
        if api_key:
            adapter_kwargs["api_key"] = api_key
        if model_path:
            adapter_kwargs["model_path"] = model_path
        if device:
            adapter_kwargs["device"] = device

        all_results = run_parallel(
            problems=problems,
            adapter_name=adapter_name,
            adapter_kwargs=adapter_kwargs,
            timeout=timeout_val,
            max_iterations=max_iters,
            real_dafny=real_dafny,
            output_dir=output_dir,
            workers=parallel,
        )

        meta = {
            "adapter": adapter_name,
            "model": model,
            "timeout": timeout_val,
            "max_iterations": max_iters,
            "workers": parallel,
            "timestamp": datetime.now().isoformat(),
        }
        save_json(all_results, meta, os.path.join(output_dir, "results.json"))
        save_csv(all_results, os.path.join(output_dir, "results.csv"))

        summary = generate_markdown_summary(all_results, adapter_name)
        summary_file = os.path.join(output_dir, "summary.md")
        with open(summary_file, "w") as f:
            f.write(summary)

        print("\n" + summary)

        all_passed = all(r["result"]["success"] for r in all_results)
        sys.exit(0 if all_passed else 1)

    # ── Sequential mode (original behaviour) ─────────────────────────
    adapter = get_adapter(
        adapter_name,
        model=model,
        base_url=base_url,
        api_key=api_key,
        model_path=model_path,
        device=device,
    )
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
            timeout=timeout_val,
            max_iterations=max_iters,
            real_dafny=real_dafny,
            output_dir=output_dir,
            skip_tests=skip_tests,
        )
        all_results.append(result)

    # Save JSON results
    results_file = os.path.join(output_dir, "results.json")
    with open(results_file, "w") as f:
        json.dump(
            {
                "adapter": adapter.name,
                "model": model,
                "timeout": timeout_val,
                "max_iterations": max_iters,
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
