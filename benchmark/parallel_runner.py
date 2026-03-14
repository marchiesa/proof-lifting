#!/usr/bin/env python3
"""
Parallel runner for the Dafny verification benchmark.

Runs multiple problems concurrently using ``concurrent.futures`` and
collects results into a single JSON/CSV summary file.

Usage:
    python parallel_runner.py \\
        --dataset ./dataset/problems \\
        --adapter openai_compatible \\
        --base-url http://localhost:8000/v1 \\
        --model meta-llama/Llama-3.1-70B-Instruct \\
        --workers 8 \\
        --max-iterations 20

Can also be driven by a YAML config file::

    python parallel_runner.py --config config.yaml
"""

import argparse
import csv
import json
import os
import signal
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional

# Add parent to path for imports.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from run_benchmark import (
    DEFAULT_REAL_DAFNY,
    PROXY_DIR,
    discover_problems,
    get_adapter,
    run_single_problem,
)


# ---------------------------------------------------------------------------
# Worker function executed in sub-processes
# ---------------------------------------------------------------------------


def _worker(
    problem: dict,
    adapter_name: str,
    adapter_kwargs: dict,
    timeout: int,
    max_iterations: int,
    real_dafny: str,
    output_dir: str,
) -> dict:
    """
    Solve a single problem in an isolated process.

    We re-create the adapter inside the subprocess because adapters may hold
    non-picklable resources (model weights, open sockets, etc.).
    """
    adapter = get_adapter(adapter_name, **adapter_kwargs)
    return run_single_problem(
        problem=problem,
        adapter=adapter,
        timeout=timeout,
        max_iterations=max_iterations,
        real_dafny=real_dafny,
        output_dir=output_dir,
    )


# ---------------------------------------------------------------------------
# Main orchestrator
# ---------------------------------------------------------------------------


def run_parallel(
    problems: List[dict],
    adapter_name: str,
    adapter_kwargs: dict,
    timeout: int,
    max_iterations: int,
    real_dafny: str,
    output_dir: str,
    workers: int,
) -> List[dict]:
    """
    Run *problems* in parallel with up to *workers* concurrent processes.

    Returns the list of result dicts (same format as ``run_single_problem``).
    """
    all_results: List[dict] = []
    futures_map: Dict = {}

    # Try to import tqdm for a progress bar; fall back to plain printing.
    try:
        from tqdm import tqdm
        pbar: Optional[object] = tqdm(total=len(problems), desc="Problems", unit="prob")
    except ImportError:
        pbar = None

    # Handle Ctrl+C gracefully.
    shutdown_requested = False
    original_sigint = signal.getsignal(signal.SIGINT)

    def _sigint_handler(signum, frame):
        nonlocal shutdown_requested
        if shutdown_requested:
            # Second Ctrl+C: hard exit.
            sys.exit(1)
        shutdown_requested = True
        print("\nShutdown requested. Waiting for running workers to finish...")

    signal.signal(signal.SIGINT, _sigint_handler)

    try:
        with ProcessPoolExecutor(max_workers=workers) as executor:
            for problem in problems:
                if shutdown_requested:
                    break
                future = executor.submit(
                    _worker,
                    problem=problem,
                    adapter_name=adapter_name,
                    adapter_kwargs=adapter_kwargs,
                    timeout=timeout,
                    max_iterations=max_iterations,
                    real_dafny=real_dafny,
                    output_dir=output_dir,
                )
                futures_map[future] = problem["name"]

            for future in as_completed(futures_map):
                name = futures_map[future]
                try:
                    result = future.result()
                    all_results.append(result)
                except Exception as exc:
                    all_results.append(
                        {
                            "problem": name,
                            "result": {
                                "success": False,
                                "iterations": 0,
                                "time_seconds": 0.0,
                                "solution_path": None,
                                "error": str(exc),
                                "timed_out": False,
                                "max_iterations_reached": False,
                                "log_path": None,
                            },
                            "status": "ERROR",
                        }
                    )
                if pbar is not None:
                    pbar.update(1)  # type: ignore[union-attr]
    finally:
        signal.signal(signal.SIGINT, original_sigint)
        if pbar is not None:
            pbar.close()  # type: ignore[union-attr]

    return all_results


# ---------------------------------------------------------------------------
# Saving helpers
# ---------------------------------------------------------------------------


def save_json(results: List[dict], meta: dict, path: str) -> None:
    """Write results and metadata to a JSON file."""
    with open(path, "w") as f:
        json.dump({**meta, "results": results}, f, indent=2)
    print(f"JSON results saved to: {path}")


def save_csv(results: List[dict], path: str) -> None:
    """Write a flat CSV summary of results."""
    fieldnames = [
        "problem",
        "status",
        "success",
        "iterations",
        "time_seconds",
        "error",
    ]
    with open(path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for r in results:
            writer.writerow(
                {
                    "problem": r["problem"],
                    "status": r.get("status", "UNKNOWN"),
                    "success": r["result"]["success"],
                    "iterations": r["result"]["iterations"],
                    "time_seconds": round(r["result"]["time_seconds"], 2),
                    "error": r["result"].get("error", ""),
                }
            )
    print(f"CSV summary saved to: {path}")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _load_config(config_path: str) -> dict:
    """Load a YAML config file, falling back to JSON."""
    try:
        import yaml  # type: ignore[import-untyped]

        with open(config_path, "r") as f:
            return yaml.safe_load(f)
    except ImportError:
        with open(config_path, "r") as f:
            return json.load(f)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Run Dafny benchmark problems in parallel"
    )
    parser.add_argument(
        "--config",
        default=None,
        help="Path to a YAML/JSON config file (overrides other flags)",
    )
    parser.add_argument("--dataset", default=None, help="Path to dataset directory")
    parser.add_argument(
        "--adapter",
        default=None,
        choices=["claude_code", "manual", "openai_compatible", "hf_transformers"],
        help="Adapter name",
    )
    parser.add_argument("--model", default="", help="Model identifier")
    parser.add_argument("--base-url", default=None, help="API base URL")
    parser.add_argument("--api-key", default=None, help="API key")
    parser.add_argument("--model-path", default=None, help="Local model path (HF)")
    parser.add_argument("--device", default="auto", help="Device for HF adapter")
    parser.add_argument("--timeout", type=int, default=600, help="Timeout per problem (s)")
    parser.add_argument("--max-iterations", type=int, default=20, help="Max dafny calls per problem")
    parser.add_argument("--real-dafny", default=DEFAULT_REAL_DAFNY, help="Real dafny command")
    parser.add_argument("--output-dir", default=None, help="Output directory")
    parser.add_argument("--workers", type=int, default=None, help="Number of parallel workers")
    parser.add_argument("--problems", nargs="*", default=None, help="Specific problem names")

    args = parser.parse_args()

    # Merge config file if provided.
    cfg: dict = {}
    if args.config:
        cfg = _load_config(args.config)

    # Resolve values: CLI > config > defaults.
    dataset = args.dataset or cfg.get("problems_dir") or cfg.get("dataset")
    adapter_name = args.adapter or cfg.get("adapter")
    model = args.model or cfg.get("model", "")
    base_url = args.base_url or cfg.get("base_url")
    api_key = args.api_key or cfg.get("api_key")
    model_path = args.model_path or cfg.get("model_path")
    device = args.device if args.device != "auto" else cfg.get("device", "auto")
    timeout_val = args.timeout if args.timeout != 600 else cfg.get("timeout", 600)
    max_iters = args.max_iterations if args.max_iterations != 20 else cfg.get("max_iterations", 20)
    real_dafny = args.real_dafny if args.real_dafny != DEFAULT_REAL_DAFNY else cfg.get("dafny_path", DEFAULT_REAL_DAFNY)
    output_dir = args.output_dir or cfg.get("output_dir")
    workers = args.workers or cfg.get("parallel_workers")
    problem_names = args.problems or cfg.get("problems")

    if not dataset:
        parser.error("--dataset is required (or set problems_dir in config)")
    if not adapter_name:
        parser.error("--adapter is required (or set adapter in config)")

    # Build adapter kwargs (used inside sub-processes).
    adapter_kwargs: dict = {"model": model}
    if base_url:
        adapter_kwargs["base_url"] = base_url
    if api_key:
        adapter_kwargs["api_key"] = api_key
    if model_path:
        adapter_kwargs["model_path"] = model_path
    if device:
        adapter_kwargs["device"] = device

    # Discover problems.
    problems = discover_problems(dataset)
    if not problems:
        print("ERROR: No problems found", file=sys.stderr)
        sys.exit(1)

    if problem_names:
        problems = [p for p in problems if p["name"] in problem_names]
        if not problems:
            print(f"ERROR: Specified problems not found: {problem_names}", file=sys.stderr)
            sys.exit(1)

    # Determine workers.
    if workers is None:
        workers = len(problems)
    print(f"Running {len(problems)} problems with {workers} parallel workers")

    # Create output directory.
    if not output_dir:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        output_dir = os.path.join(
            os.path.dirname(os.path.abspath(__file__)),
            "results",
            f"{adapter_name}_{timestamp}",
        )
    os.makedirs(output_dir, exist_ok=True)

    start_wall = time.time()

    results = run_parallel(
        problems=problems,
        adapter_name=adapter_name,
        adapter_kwargs=adapter_kwargs,
        timeout=timeout_val,
        max_iterations=max_iters,
        real_dafny=real_dafny,
        output_dir=output_dir,
        workers=workers,
    )

    wall_time = time.time() - start_wall

    meta = {
        "adapter": adapter_name,
        "model": model,
        "timeout": timeout_val,
        "max_iterations": max_iters,
        "workers": workers,
        "wall_time_seconds": round(wall_time, 2),
        "timestamp": datetime.now().isoformat(),
    }

    # Save results.
    save_json(results, meta, os.path.join(output_dir, "results.json"))
    save_csv(results, os.path.join(output_dir, "results.csv"))

    # Print summary.
    solved = sum(1 for r in results if r["result"]["success"])
    total = len(results)
    print(f"\nSolved: {solved}/{total}")
    print(f"Wall time: {wall_time:.1f}s")
    for r in sorted(results, key=lambda x: x["problem"]):
        status = r.get("status", "UNKNOWN")
        iters = r["result"]["iterations"]
        t = r["result"]["time_seconds"]
        print(f"  {r['problem']:30s}  {status:10s}  iters={iters:3d}  time={t:.1f}s")

    sys.exit(0 if solved == total else 1)


if __name__ == "__main__":
    main()
