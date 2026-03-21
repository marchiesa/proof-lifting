#!/usr/bin/env python3
from __future__ import annotations
"""
Analyze benchmark results: per-model stats, failure analysis, attempt distribution.

Produces a summary showing that failures are genuine (not infrastructure issues)
and that models have exhausted their reasoning capacity.

Usage:
    python3 analyze_results.py                          # all models in results/
    python3 analyze_results.py --dir results/gpt-oss-20b
    python3 analyze_results.py --compare                # side-by-side comparison
"""

import argparse
import json
import os
import re
import sys
from collections import Counter
from pathlib import Path

RESULTS_BASE = Path(__file__).parent / "results"

# Quirk type patterns
QUIRK_PATTERNS = {
    "B1": [r"\[\.\.[\|]\w+[\|]\]\s*==\s*\w+", r"\[\.\..*\+\s*1\]\s*==\s*\w+\[\.\."],
    "A2": [r"^assert\s+[A-Z]\w+\("],
    "A1": [r"^assert\s+exists"],
    "C1": [r"[%/]"],
    "D4": [r"^assert\s+false\s*;"],
}


def classify_problem_types(problem_name: str, ablation_dir: Path) -> set:
    """Get quirk types for a problem from ablation data."""
    r = ablation_dir / problem_name / "ablation" / "results.json"
    if not r.exists():
        return set()
    data = json.loads(r.read_text())
    types = set()
    for a in data["results"]:
        if not a.get("essential"):
            continue
        text = a.get("text", "").strip()
        matched = False
        for cat, pats in QUIRK_PATTERNS.items():
            for p in pats:
                if re.search(p, text):
                    types.add(cat)
                    matched = True
                    break
        if not matched:
            types.add("other")
    return types


def analyze_model(results_dir: Path, ablation_dir: Path | None = None) -> dict:
    """Analyze results for one model."""
    problems = []
    for d in sorted(results_dir.iterdir()):
        rp = d / "result.json"
        if not rp.exists():
            continue
        r = json.loads(rp.read_text())

        # Classify failure reasons per attempt
        verify_fail = 0
        spec_fail = 0
        body_fail = 0
        no_code = 0
        llm_error = 0
        has_assume = False

        for a in r.get("attempts", []):
            sc = str(a.get("spec_check", ""))
            if a.get("llm_error") or (not a.get("llm_response") and not a.get("extracted_code")):
                llm_error += 1
            elif not a.get("extracted_code"):
                no_code += 1
            elif "body changed" in sc:
                body_fail += 1
            elif "differ" in sc or "Missing" in sc:
                spec_fail += 1
            elif a.get("dafny_success") is False:
                verify_fail += 1

        # Check for assume in verified code
        code = r.get("verified_code", "")
        if code and re.search(r"^\s*assume\b", code, re.MULTILINE | re.IGNORECASE):
            has_assume = True

        # Get quirk types
        types = set()
        if ablation_dir:
            types = classify_problem_types(d.name, ablation_dir)

        problems.append({
            "problem": d.name,
            "success": r.get("success", False),
            "attempts": r.get("total_attempts", 0),
            "time": r.get("total_time", 0),
            "tokens": r.get("total_tokens", 0),
            "essential_count": r.get("essential_count", 0),
            "verify_fail": verify_fail,
            "spec_fail": spec_fail,
            "body_fail": body_fail,
            "no_code": no_code,
            "llm_error": llm_error,
            "has_assume": has_assume,
            "quirk_types": sorted(types),
        })

    passed = [p for p in problems if p["success"]]
    failed = [p for p in problems if not p["success"]]

    # Attempt distribution for failures
    fail_attempts = [p["attempts"] for p in failed]
    pass_attempts = [p["attempts"] for p in passed]

    # Failure reason totals
    total_fail_attempts = sum(p["verify_fail"] + p["spec_fail"] + p["body_fail"] + p["no_code"] + p["llm_error"]
                              for p in failed)
    total_verify = sum(p["verify_fail"] for p in failed)
    total_spec = sum(p["spec_fail"] for p in failed)
    total_body = sum(p["body_fail"] for p in failed)
    total_nocode = sum(p["no_code"] for p in failed)
    total_llmerr = sum(p["llm_error"] for p in failed)

    # Per-type pass rates
    type_pass = Counter()
    type_total = Counter()
    for p in problems:
        for t in p["quirk_types"]:
            type_total[t] += 1
            if p["success"]:
                type_pass[t] += 1

    report = {
        "model": results_dir.name,
        "total_problems": len(problems),
        "passed": len(passed),
        "failed": len(failed),
        "pass_rate": round(100 * len(passed) / len(problems), 1) if problems else 0,

        "pass_attempts": {
            "values": sorted(pass_attempts),
            "mean": round(sum(pass_attempts) / len(pass_attempts), 1) if pass_attempts else 0,
            "median": sorted(pass_attempts)[len(pass_attempts) // 2] if pass_attempts else 0,
            "min": min(pass_attempts) if pass_attempts else 0,
            "max": max(pass_attempts) if pass_attempts else 0,
        },
        "fail_attempts": {
            "values": sorted(fail_attempts),
            "mean": round(sum(fail_attempts) / len(fail_attempts), 1) if fail_attempts else 0,
            "median": sorted(fail_attempts)[len(fail_attempts) // 2] if fail_attempts else 0,
            "min": min(fail_attempts) if fail_attempts else 0,
            "max": max(fail_attempts) if fail_attempts else 0,
            "total": sum(fail_attempts),
        },

        "failure_reasons": {
            "total_attempts": total_fail_attempts,
            "verify_fail": total_verify,
            "spec_changed": total_spec,
            "body_changed": total_body,
            "no_code_extracted": total_nocode,
            "llm_error": total_llmerr,
            "verify_fail_pct": round(100 * total_verify / total_fail_attempts, 1) if total_fail_attempts else 0,
        },

        "assume_cheats": sum(1 for p in problems if p["has_assume"]),

        "by_quirk_type": {
            t: {"pass": type_pass.get(t, 0), "total": type_total[t],
                "rate": round(100 * type_pass.get(t, 0) / type_total[t], 1)}
            for t in sorted(type_total.keys())
        },

        "problems": problems,
    }

    return report


def print_report(report: dict):
    """Print human-readable report."""
    print(f"\n{'='*60}")
    print(f"Model: {report['model']}")
    print(f"{'='*60}")
    print(f"Pass: {report['passed']}/{report['total_problems']} ({report['pass_rate']}%)")
    print(f"Assume cheats: {report['assume_cheats']}")

    print(f"\nSuccessful problems ({report['passed']}):")
    pa = report["pass_attempts"]
    if pa["values"]:
        print(f"  Attempts: mean={pa['mean']}, median={pa['median']}, range=[{pa['min']}, {pa['max']}]")
        print(f"  Distribution: {pa['values']}")

    print(f"\nFailed problems ({report['failed']}):")
    fa = report["fail_attempts"]
    if fa["values"]:
        print(f"  Attempts: mean={fa['mean']}, median={fa['median']}, range=[{fa['min']}, {fa['max']}]")
        print(f"  Total attempts on failed: {fa['total']}")

    fr = report["failure_reasons"]
    if fr["total_attempts"]:
        print(f"\n  Failure breakdown ({fr['total_attempts']} total failed attempts):")
        print(f"    Verification failed:  {fr['verify_fail']} ({fr['verify_fail_pct']}%)")
        print(f"    Spec changed:         {fr['spec_changed']}")
        print(f"    Body changed:         {fr['body_changed']}")
        print(f"    No code extracted:    {fr['no_code_extracted']}")
        print(f"    LLM error:            {fr['llm_error']}")

    if report["by_quirk_type"]:
        print(f"\n  By quirk type (programs containing type):")
        for t, info in report["by_quirk_type"].items():
            print(f"    {t}: {info['pass']}/{info['total']} ({info['rate']}%)")


def main():
    parser = argparse.ArgumentParser(description="Analyze benchmark results")
    parser.add_argument("--dir", help="Specific results directory")
    parser.add_argument("--compare", action="store_true", help="Side-by-side comparison")
    parser.add_argument("--output", help="Output JSON path")
    parser.add_argument("--ablation-dir", default=None, help="Ablation results dir for type info")
    args = parser.parse_args()

    ablation_dir = Path(args.ablation_dir) if args.ablation_dir else Path(__file__).parent.parent / "results"

    if args.dir:
        dirs = [Path(args.dir)]
    else:
        dirs = [d for d in sorted(RESULTS_BASE.iterdir()) if d.is_dir()]

    reports = []
    for d in dirs:
        report = analyze_model(d, ablation_dir)
        reports.append(report)
        print_report(report)

    if args.compare and len(reports) > 1:
        print(f"\n{'='*60}")
        print("COMPARISON")
        print(f"{'='*60}")
        header = f"{'Model':<25s} {'Pass':>6s} {'Rate':>6s} {'Fail att':>10s} {'Verify%':>8s} {'Assume':>7s}"
        print(header)
        print("-" * len(header))
        for r in reports:
            fa = r["fail_attempts"]
            fr = r["failure_reasons"]
            print(f"{r['model']:<25s} {r['passed']:>3d}/{r['total_problems']:<2d} {r['pass_rate']:>5.1f}% {fa['mean']:>10.0f} {fr['verify_fail_pct']:>7.1f}% {r['assume_cheats']:>7d}")

    if args.output:
        Path(args.output).write_text(json.dumps(reports, indent=2, default=str))
        print(f"\nSaved to: {args.output}")


if __name__ == "__main__":
    main()
