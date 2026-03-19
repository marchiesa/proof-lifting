#!/usr/bin/env python3
"""Re-run ablation across all problems using fixed extract/create logic.

Fixes from the original run:
  1. Handles `assert ... by { ... }` blocks (comments out entire block)
  2. Rejects parse_error as "essential" — only real verification
     failures (error or timeout) count.

Note: the prover_error category (from Boogie's model parser crashing on
counterexamples with "0.0") is no longer possible — that locale bug was
fixed in our modified Boogie (CultureInfo.InvariantCulture in Model.cs).
The detection is kept as a safety net but should never trigger.

Usage:
    python3 smt_analysis/rerun_ablation.py [--problems P1 P2 ...] [--parallel N]
"""

import argparse
import json
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

PROJ_ROOT = Path(__file__).parent.parent.resolve()
RESULTS_DIR = PROJ_ROOT / "smt_analysis" / "results"
ABLATION_SH = PROJ_ROOT / "smt_analysis" / "helpers" / "run_ablation.sh"

# ---------------------------------------------------------------------------
# Assert extraction (same logic as fixed ablate_and_diagnose.py)
# ---------------------------------------------------------------------------

def extract_asserts(dfy_path: Path) -> list[dict]:
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


def create_variant(dfy_path: Path, assert_info: dict, output_path: Path):
    lines = dfy_path.read_text().splitlines(keepends=True)
    start = assert_info["line_idx"]
    end = assert_info.get("end_idx", start)
    for idx in range(start, end + 1):
        lines[idx] = f"// REMOVED: {lines[idx]}"
    output_path.write_text("".join(lines))


# ---------------------------------------------------------------------------
# Run one ablation variant
# ---------------------------------------------------------------------------

def run_one_variant(variant_path: Path, timeout: int = 60) -> dict:
    try:
        result = subprocess.run(
            ["bash", str(ABLATION_SH), str(variant_path), str(timeout)],
            capture_output=True, text=True, timeout=timeout + 60,
        )
        try:
            data = json.loads(result.stdout)
        except json.JSONDecodeError:
            data = {"result": "parse_error", "raw_output": result.stdout[:500]}
    except subprocess.TimeoutExpired:
        data = {"result": "timeout", "errors": ["process timeout"]}

    return data


# ---------------------------------------------------------------------------
# Ablate one problem
# ---------------------------------------------------------------------------

def ablate_problem(problem_dir: Path, timeout: int = 60) -> dict | None:
    """Run ablation on a single problem. Returns results dict or None."""
    dfy = problem_dir / "verified.dfy"
    if not dfy.exists():
        return None

    ablation_dir = problem_dir / "ablation_rerun"
    ablation_dir.mkdir(parents=True, exist_ok=True)

    asserts = extract_asserts(dfy)
    if not asserts:
        summary = {"problem": problem_dir.name, "total": 0, "essential_count": 0, "results": []}
        (ablation_dir / "results.json").write_text(json.dumps(summary, indent=2))
        return summary

    results = []
    for a in asserts:
        variant_path = ablation_dir / f"without_{a['index']:02d}.dfy"
        create_variant(dfy, a, variant_path)
        data = run_one_variant(variant_path, timeout)

        ablation_result = data.get("result", "unknown")

        # Only real verification failures count as essential
        essential = ablation_result in ("error", "timeout")
        # parse_error = syntax error in the variant (bug in variant creation)
        # prover_error = Boogie model parser crash (locale bug, now fixed)
        if ablation_result in ("parse_error", "prover_error"):
            essential = False

        results.append({
            "index": a["index"],
            "line": a["line"],
            "end_line": a.get("end_idx", a["line_idx"]) + 1,
            "text": a["text"][:200],
            "ablation_result": ablation_result,
            "ablation_time": data.get("time_seconds", 0),
            "essential": essential,
            "ablation_errors": data.get("errors", []),
        })

    essential_count = sum(1 for r in results if r["essential"])
    summary = {
        "problem": problem_dir.name,
        "total": len(results),
        "essential_count": essential_count,
        "results": results,
    }
    (ablation_dir / "results.json").write_text(json.dumps(summary, indent=2))
    return summary


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--problems", nargs="*", help="Specific problem dirs to run")
    parser.add_argument("--parallel", type=int, default=4, help="Parallel workers")
    parser.add_argument("--timeout", type=int, default=60, help="Per-verification timeout")
    args = parser.parse_args()

    if args.problems:
        problem_dirs = [RESULTS_DIR / p for p in args.problems]
    else:
        problem_dirs = sorted(
            d for d in RESULTS_DIR.iterdir()
            if d.is_dir() and (d / "verified.dfy").exists()
        )

    print(f"Running ablation on {len(problem_dirs)} problems (parallel={args.parallel}, timeout={args.timeout}s)")

    all_summaries = []
    total_essential = 0
    total_asserts = 0
    problems_with_essential = 0

    for i, pdir in enumerate(problem_dirs):
        t0 = time.time()
        summary = ablate_problem(pdir, args.timeout)
        elapsed = time.time() - t0

        if summary is None:
            print(f"[{i+1:3d}/{len(problem_dirs)}] {pdir.name}: no verified.dfy, skipped")
            continue

        n_ess = summary["essential_count"]
        n_tot = summary["total"]
        total_essential += n_ess
        total_asserts += n_tot
        if n_ess > 0:
            problems_with_essential += 1

        tag = f"{n_ess}/{n_tot} essential" if n_tot > 0 else "no asserts"
        print(f"[{i+1:3d}/{len(problem_dirs)}] {pdir.name}: {tag}  ({elapsed:.1f}s)")

        # Show essential assertions
        for r in summary["results"]:
            if r["essential"]:
                print(f"    line {r['line']}: {r['text'][:90]}")
            elif r["ablation_result"] in ("parse_error", "prover_error"):
                print(f"    line {r['line']}: SKIPPED ({r['ablation_result']}) {r['text'][:70]}")

        all_summaries.append(summary)

    # Write global summary
    global_summary = {
        "total_problems": len(problem_dirs),
        "problems_with_essential": problems_with_essential,
        "total_asserts": total_asserts,
        "total_essential": total_essential,
        "per_problem": {s["problem"]: {
            "total": s["total"],
            "essential": s["essential_count"],
            "essential_asserts": [r for r in s["results"] if r["essential"]],
        } for s in all_summaries},
    }
    out_path = RESULTS_DIR / "ablation_rerun_summary.json"
    out_path.write_text(json.dumps(global_summary, indent=2))
    print(f"\n=== TOTALS ===")
    print(f"Problems: {len(problem_dirs)}")
    print(f"Problems with essential asserts: {problems_with_essential}")
    print(f"Total asserts: {total_asserts}")
    print(f"Essential asserts: {total_essential}")
    print(f"Summary written to: {out_path}")


if __name__ == "__main__":
    main()
