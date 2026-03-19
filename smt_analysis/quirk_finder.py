#!/usr/bin/env python3
"""
SMT Quirk Extraction Pipeline — Orchestrator.

Spawns a Claude Code instance per problem to:
  1. VERIFY (add invariants)
  2. ANNOTATE (SMT→Dafny names)
  3. ABLATE (find essential assertions)
  4. DIAGNOSE (investigate each essential assertion)
  5. REPORT (structured findings)

Then runs a final CLASSIFY phase across all reports.

Usage:
    # Run on specific problems
    python3 smt_analysis/quirk_finder.py --problems 0 1 2

    # Run on all problems
    python3 smt_analysis/quirk_finder.py --all

    # Run only the classify phase (after per-problem runs)
    python3 smt_analysis/quirk_finder.py --classify-only

    # Customize parallelism and timeouts
    python3 smt_analysis/quirk_finder.py --all --workers 5 --timeout 900
"""

import argparse
import json
import os
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

PROJ_ROOT = Path(__file__).parent.parent.resolve()
DATASET_DIR = PROJ_ROOT / "dataset"
RESULTS_DIR = PROJ_ROOT / "smt_analysis" / "results"
PROMPT_FILE = PROJ_ROOT / "smt_analysis" / "prompt.md"


def get_problem_dirs() -> list[Path]:
    """List all problem directories in dataset/."""
    dirs = sorted(DATASET_DIR.iterdir())
    return [d for d in dirs if d.is_dir() and (d / "task.dfy").exists()]


def get_problem_id(problem_dir: Path) -> str:
    """Extract problem ID from directory name."""
    return problem_dir.name


def build_prompt(problem_dir: Path, verify_only: bool = False, analyze_only: bool = False) -> str:
    """Build the prompt for a Claude Code instance."""
    task_file = problem_dir / "task.dfy"
    task_content = task_file.read_text()

    problem_id = get_problem_id(problem_dir)
    result_dir = RESULTS_DIR / problem_id

    # Load problem description if available
    problem_desc = ""
    problem_json = problem_dir / "problem.json"
    if problem_json.exists():
        try:
            p = json.loads(problem_json.read_text())
            problem_desc = f"\n## Problem: {p.get('title', problem_id)}\n{p.get('description', '')}\n"
        except json.JSONDecodeError:
            pass

    if verify_only:
        dotnet = os.environ.get("DOTNET8", os.environ.get("DOTNET", "dotnet"))
        dafny_dll = PROJ_ROOT / "dafny-source" / "Binaries" / "Dafny.dll"
        return f"""Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.
{problem_desc}
## File: {task_file}

```dafny
{task_content}
```

## Instructions:

1. Read the code carefully. Understand what the method does and what the spec requires.

2. Add loop invariants for every loop. Common patterns:
   - Bounds: `invariant 0 <= i <= |s|`
   - Accumulator: `invariant acc == F(s[..i])` for recursive ghost functions
   - Sequence slicing: `assert s[..i+1] == s[..i] + [s[i]];` before using F(s[..i+1])
   - Full slice identity: `assert s[..|s|] == s;` after loops that process entire sequences
   - Type preservation: `invariant AllNonNeg(s[..i])` if needed by the spec

3. Add helper lemmas if needed (e.g., SumAppend, induction lemmas).

4. Run dafny verify:
   ```bash
   {dotnet} {dafny_dll} verify {result_dir}/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `{result_dir}/verified.dfy`.
   Also write `{result_dir}/verify_result.json`:
   ```json
   {{
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }}
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to {result_dir}/ (create the directory if needed).
"""

    # Full quirk analysis prompt
    prompt_template = PROMPT_FILE.read_text()
    prompt = prompt_template.replace("PROJ_ROOT", str(PROJ_ROOT))
    prompt = prompt.replace("PROBLEM_DIR", str(result_dir))

    # Set mode
    mode = "ANALYZE_ONLY" if analyze_only else "FULL"
    prompt = prompt.replace("%%MODE%%", mode)

    # Include verified.dfy content if in analyze-only mode
    verified_section = ""
    verified_file = result_dir / "verified.dfy"
    if analyze_only and verified_file.exists():
        verified_content = verified_file.read_text()
        verified_section = f"""
## ALREADY VERIFIED — DO NOT RE-VERIFY

The file `{result_dir}/verified.dfy` already exists and verifies correctly.
**DO NOT add invariants or modify verified.dfy.** Go directly to Phase 2 (ANNOTATE).

Your first step: run full logging to produce artifacts:
```bash
mkdir -p {result_dir}/artifacts
cp {result_dir}/verified.dfy {result_dir}/artifacts/verified.dfy
bash {PROJ_ROOT}/smt_analysis/helpers/run_dafny_verify.sh {result_dir}/artifacts/verified.dfy {result_dir}/artifacts/ 60
```

Then continue with Phase 2 (ANNOTATE), Phase 3 (ABLATE), Phase 4 (DIAGNOSE), Phase 5 (AXIOM), Phase 6 (REPORT).

Here is the verified file for reference:

```dafny
{verified_content}
```
"""

    full_prompt = f"""# Problem: {problem_id}

## Task file ({task_file})

```dafny
{task_content}
```
{verified_section}
## Output directory: {result_dir}

IMPORTANT PATHS:
- PROJ_ROOT = {PROJ_ROOT}
- PROBLEM_DIR = {result_dir}
- Original task: {task_file}

{prompt}
"""
    return full_prompt


def run_problem(problem_dir: Path, timeout: int = 900, verify_only: bool = False, analyze_only: bool = False) -> dict:
    """Run Claude Code on a single problem. Returns result dict."""
    problem_id = get_problem_id(problem_dir)
    result_dir = RESULTS_DIR / problem_id
    result_dir.mkdir(parents=True, exist_ok=True)
    if not verify_only:
        (result_dir / "artifacts").mkdir(exist_ok=True)
        (result_dir / "attempts").mkdir(exist_ok=True)
        (result_dir / "evidence").mkdir(exist_ok=True)

    # Copy task.dfy to results
    task_src = problem_dir / "task.dfy"
    task_dst = result_dir / "task.dfy"
    task_dst.write_text(task_src.read_text())

    # Build prompt
    prompt = build_prompt(problem_dir, verify_only=verify_only, analyze_only=analyze_only)

    # Save prompt for debugging
    (result_dir / "agent_prompt.md").write_text(prompt)

    print(f"[{problem_id}] Starting Claude Code instance...")
    t0 = time.time()

    try:
        result = subprocess.run(
            [
                "claude",
                "-p",
                "--dangerously-skip-permissions",
                "--no-session-persistence",
                "--output-format", "json",
                "--verbose",
                "--max-turns", "50",
            ],
            input=prompt,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=str(result_dir),
        )

        elapsed = time.time() - t0

        # Save raw output
        (result_dir / "claude_stdout.txt").write_text(result.stdout)
        (result_dir / "claude_stderr.txt").write_text(result.stderr)

        # Try to parse JSON output
        claude_result = None
        try:
            claude_result = json.loads(result.stdout)
        except json.JSONDecodeError:
            pass

        # Check if report.json was produced
        report_file = result_dir / "report.json"
        report = None
        if report_file.exists():
            try:
                report = json.loads(report_file.read_text())
            except json.JSONDecodeError:
                pass

        status = {
            "problem_id": problem_id,
            "elapsed_seconds": round(elapsed, 1),
            "exit_code": result.returncode,
            "report_generated": report is not None,
            "solved": report.get("solved", False) if report else False,
        }

        print(
            f"[{problem_id}] Done in {elapsed:.0f}s — "
            f"{'SOLVED' if status['solved'] else 'UNSOLVED'} "
            f"(exit={result.returncode})"
        )

        return status

    except subprocess.TimeoutExpired:
        elapsed = time.time() - t0
        print(f"[{problem_id}] TIMEOUT after {elapsed:.0f}s")
        return {
            "problem_id": problem_id,
            "elapsed_seconds": round(elapsed, 1),
            "exit_code": -1,
            "report_generated": False,
            "solved": False,
            "error": "timeout",
        }

    except Exception as e:
        elapsed = time.time() - t0
        print(f"[{problem_id}] ERROR: {e}")
        return {
            "problem_id": problem_id,
            "elapsed_seconds": round(elapsed, 1),
            "exit_code": -1,
            "report_generated": False,
            "solved": False,
            "error": str(e),
        }


def run_all_problems(
    problem_indices: list[int] | None,
    max_workers: int = 3,
    timeout: int = 900,
    verify_only: bool = False,
    analyze_only: bool = False,
    skip_verified: bool = False,
    skip_analyzed: bool = False,
    problem_names: list[str] | None = None,
):
    """Run Claude Code on all (or selected) problems."""
    all_dirs = get_problem_dirs()

    if problem_names is not None:
        name_set = set(problem_names)
        dirs = [d for d in all_dirs if d.name in name_set]
    elif problem_indices is not None:
        dirs = [all_dirs[i] for i in problem_indices if i < len(all_dirs)]
    else:
        dirs = all_dirs

    if analyze_only:
        # Only run on problems that are already verified
        before = len(dirs)
        dirs = [d for d in dirs if (RESULTS_DIR / d.name / "verified.dfy").exists()]
        skipped = before - len(dirs)
        if skipped > 0:
            print(f"Skipping {skipped} unverified problems (analyze-only mode)")

        # Inline non-recursive lemmas before analysis
        from smt_analysis.inline_lemmas import process_problem as inline_problem
        print("Inlining non-recursive lemmas...")
        inline_results = []
        for d in dirs:
            r = inline_problem(d.name)
            if r["status"] == "inlined":
                inline_results.append(r)
        if inline_results:
            print(f"  Inlined lemmas in {len(inline_results)} problems")
        else:
            print(f"  No lemmas to inline")
        if skip_analyzed:
            before = len(dirs)
            dirs = [d for d in dirs if not (RESULTS_DIR / d.name / "report.json").exists()]
            skipped = before - len(dirs)
            if skipped > 0:
                print(f"Skipping {skipped} already-analyzed problems")
    elif skip_verified:
        before = len(dirs)
        dirs = [d for d in dirs if not (RESULTS_DIR / d.name / "verified.dfy").exists()]
        skipped = before - len(dirs)
        if skipped > 0:
            print(f"Skipping {skipped} already-verified problems")

    if analyze_only:
        mode = "ANALYZE-ONLY (steps 2-6)"
    elif verify_only:
        mode = "VERIFY-ONLY"
    else:
        mode = "FULL ANALYSIS"
    print(f"Running {len(dirs)} problems [{mode}] with {max_workers} workers, {timeout}s timeout")
    print(f"Results dir: {RESULTS_DIR}")
    print()

    RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    results = []
    t0 = time.time()

    if max_workers == 1:
        # Sequential execution
        for d in dirs:
            r = run_problem(d, timeout, verify_only=verify_only, analyze_only=analyze_only)
            results.append(r)
    else:
        # Parallel execution
        with ProcessPoolExecutor(max_workers=max_workers) as executor:
            futures = {executor.submit(run_problem, d, timeout, verify_only, analyze_only): d for d in dirs}
            for future in as_completed(futures):
                r = future.result()
                results.append(r)

    elapsed = time.time() - t0

    # Summary
    solved = sum(1 for r in results if r["solved"])
    reported = sum(1 for r in results if r["report_generated"])

    print()
    print("=" * 60)
    print(f"SUMMARY: {solved}/{len(results)} solved, {reported}/{len(results)} reports generated")
    print(f"Total time: {elapsed:.0f}s")
    print("=" * 60)

    # Save overall results
    summary_file = RESULTS_DIR / "run_summary.json"
    summary = {
        "total_problems": len(results),
        "solved": solved,
        "reports_generated": reported,
        "total_time_seconds": round(elapsed, 1),
        "per_problem": results,
    }
    summary_file.write_text(json.dumps(summary, indent=2))
    print(f"Summary: {summary_file}")

    return results


def run_classify():
    """Run the classify phase across all reports."""
    print("Running classification phase...")
    classify_script = PROJ_ROOT / "smt_analysis" / "classify.py"

    result = subprocess.run(
        [sys.executable, str(classify_script)],
        capture_output=True,
        text=True,
        timeout=300,
        cwd=str(PROJ_ROOT),
    )

    print(result.stdout)
    if result.stderr:
        print(result.stderr, file=sys.stderr)

    return result.returncode == 0


def main():
    parser = argparse.ArgumentParser(
        description="SMT Quirk Extraction Pipeline — Orchestrator"
    )
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument(
        "--problems",
        type=int,
        nargs="+",
        help="Problem indices to run (0-based)",
    )
    group.add_argument("--all", action="store_true", help="Run all problems")
    group.add_argument(
        "--names",
        type=str,
        nargs="+",
        help="Problem names to run (e.g., 0000_1013_A)",
    )
    group.add_argument(
        "--classify-only",
        action="store_true",
        help="Only run the classification phase",
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=3,
        help="Max parallel Claude Code instances (default: 3)",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=900,
        help="Timeout per problem in seconds (default: 900)",
    )
    parser.add_argument(
        "--no-classify",
        action="store_true",
        help="Skip classification phase after per-problem runs",
    )
    parser.add_argument(
        "--verify-only",
        action="store_true",
        help="Only verify (add invariants), skip ablation/diagnosis/annotation",
    )
    parser.add_argument(
        "--analyze-only",
        action="store_true",
        help="Skip verification, run steps 2-6 (annotate/ablate/diagnose/axiom/report) on already-verified problems",
    )
    parser.add_argument(
        "--skip-verified",
        action="store_true",
        help="Skip problems that already have a verified.dfy in results",
    )
    parser.add_argument(
        "--skip-analyzed",
        action="store_true",
        help="Skip problems that already have a report.json in results",
    )
    args = parser.parse_args()

    if args.classify_only:
        success = run_classify()
        sys.exit(0 if success else 1)

    # Run per-problem phase
    indices = None if (args.all or args.names) else args.problems
    results = run_all_problems(
        indices, args.workers, args.timeout,
        verify_only=args.verify_only,
        analyze_only=args.analyze_only,
        skip_verified=args.skip_verified,
        skip_analyzed=args.skip_analyzed,
        problem_names=args.names if hasattr(args, 'names') else None,
    )

    # Run classification (skip in verify-only mode)
    if not args.no_classify and not args.verify_only:
        reports = sum(1 for r in results if r["report_generated"])
        if reports > 0:
            print()
            run_classify()
        else:
            print("No reports generated — skipping classification.")


if __name__ == "__main__":
    main()
