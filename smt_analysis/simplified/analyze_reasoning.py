#!/usr/bin/env python3
from __future__ import annotations
"""
Analyze LLM reasoning traces on simplified quirk examples.

For each result, classifies the reasoning as:
  - "derivation": the model unfolds definitions, performs step-by-step
    algebraic reasoning (calc-style), derives WHY the assertion is needed
  - "pattern_recognition": the model recognizes the code pattern and
    knows the assertion from training data, without deriving it
  - "comment_reading": the model reads the "// REMOVED:" comment and
    copies back the assertion verbatim
  - "no_reasoning": no reasoning trace captured
  - "failed": the model failed to solve the problem

Outputs a JSON report and human-readable summary.

Usage:
    python3 analyze_reasoning.py                              # all models
    python3 analyze_reasoning.py --model gpt-oss-20b-thinking
"""

import argparse
import json
import re
import sys
from pathlib import Path

RESULTS_DIR = Path(__file__).parent / "results"

# Indicators of actual derivation (calc-style reasoning)
DERIVATION_KEYWORDS = [
    r"unfold",
    r"expand",
    r"by definition",
    r"substitut",
    r"rewrit",
    r"simplif",
    r"Sum\(.+\)\s*[=]\s*Sum\(",  # unfolding Sum(a[..i+1]) = Sum(...)
    r"Seq#Take|Seq#Append|Seq#Build",  # SMT-level reasoning
    r"extensionality",
    r"axiom",
    r"e-graph|e-matching|trigger",
    r"calc\s*\{",
    r"step.by.step",
    r"because.*=.*=",  # chain of equalities
]

# Indicators of pattern recognition (memorized)
PATTERN_KEYWORDS = [
    r"classic|standard|well.known|common pattern",
    r"property of sequences",
    r"needed to prove invariant",
    r"needed for.*loop",
    r"helps? (the )?(dafny |)verif",
    r"we need to (add|insert|assert)",
    r"the missing assert",
]


def classify_reasoning(reasoning: str, response: str, quirk_type: str) -> dict:
    """Classify a reasoning trace."""
    if not reasoning:
        return {
            "classification": "no_reasoning",
            "evidence": "No reasoning trace captured",
            "derivation_score": 0,
            "pattern_score": 0,
        }

    reasoning_lower = reasoning.lower()

    # Count derivation indicators
    derivation_hits = []
    for kw in DERIVATION_KEYWORDS:
        matches = re.findall(kw, reasoning, re.IGNORECASE)
        if matches:
            derivation_hits.extend(matches)

    # Count pattern recognition indicators
    pattern_hits = []
    for kw in PATTERN_KEYWORDS:
        matches = re.findall(kw, reasoning, re.IGNORECASE)
        if matches:
            pattern_hits.extend(matches)

    # Check for actual algebraic steps (e.g., Sum(a[..i+1]) = Sum(a[..i]) + a[i])
    has_algebraic_chain = bool(re.search(
        r"Sum\(.+\)\s*=\s*Sum\(.+\)\s*\+", reasoning)) or bool(re.search(
        r"=.*=.*=", reasoning))

    # Check for SMT-level understanding
    has_smt_understanding = bool(re.search(
        r"Z3|SMT|solver|e-match|trigger|axiom|quantifier.*instantiat",
        reasoning, re.IGNORECASE))

    derivation_score = len(derivation_hits) + (2 if has_algebraic_chain else 0) + (2 if has_smt_understanding else 0)
    pattern_score = len(pattern_hits)

    if derivation_score >= 3 and has_algebraic_chain:
        classification = "derivation"
        evidence = f"Algebraic chain found, {len(derivation_hits)} derivation indicators"
    elif derivation_score > pattern_score and derivation_score >= 2:
        classification = "derivation"
        evidence = f"{len(derivation_hits)} derivation indicators vs {len(pattern_hits)} pattern indicators"
    elif pattern_score > 0:
        classification = "pattern_recognition"
        evidence = f"{len(pattern_hits)} pattern indicators, {len(derivation_hits)} derivation indicators"
    else:
        classification = "pattern_recognition"
        evidence = "No strong derivation indicators found"

    return {
        "classification": classification,
        "evidence": evidence,
        "derivation_score": derivation_score,
        "pattern_score": pattern_score,
        "derivation_hits": derivation_hits[:5],
        "pattern_hits": pattern_hits[:5],
        "has_algebraic_chain": has_algebraic_chain,
        "has_smt_understanding": has_smt_understanding,
        "reasoning_length": len(reasoning),
    }


def extract_reasoning_from_response(response: str) -> str:
    """Extract reasoning from response text.

    Some models embed thinking in the response itself using tags like
    ◁think▷...◁/think▷ or <think>...</think> rather than a separate field.
    """
    # Try various thinking tag formats
    for pattern in [
        r'◁think▷(.*?)(?:◁/think▷|<DAFNY_CODE>|```)',
        r'<think>(.*?)(?:</think>|<DAFNY_CODE>|```)',
        r'<thinking>(.*?)(?:</thinking>|<DAFNY_CODE>|```)',
    ]:
        m = re.search(pattern, response, re.DOTALL)
        if m:
            return m.group(1).strip()
    return ""


def analyze_model(model_dir: Path) -> dict:
    """Analyze all results for one model."""
    results = []

    for type_dir in sorted(model_dir.iterdir()):
        result_path = type_dir / "result.json"
        if not result_path.exists():
            continue

        r = json.loads(result_path.read_text())
        if not r.get("attempts"):
            continue

        # Use the successful attempt, or the last attempt
        attempt = None
        for a in r["attempts"]:
            if a.get("dafny_success"):
                attempt = a
                break
        if not attempt:
            attempt = r["attempts"][-1]

        reasoning = attempt.get("llm_reasoning", "")
        response = attempt.get("llm_response", "")

        # If no reasoning field, try extracting from response text
        if not reasoning and response:
            reasoning = extract_reasoning_from_response(response)

        analysis = classify_reasoning(reasoning, response, type_dir.name)
        analysis["type"] = type_dir.name
        analysis["success"] = r.get("success", False)
        analysis["attempts"] = r.get("total_attempts", 0)
        analysis["reasoning_text"] = reasoning

        results.append(analysis)

    # Summary
    by_class = {}
    for r in results:
        c = r["classification"]
        by_class.setdefault(c, []).append(r["type"])

    return {
        "model": model_dir.name,
        "total_types": len(results),
        "by_classification": {k: len(v) for k, v in by_class.items()},
        "details": results,
    }


def aggregate_runs(model_name: str, run_dirs: list[Path]) -> dict:
    """Aggregate reasoning analysis across multiple runs."""
    from collections import Counter, defaultdict

    # Per-type: collect classifications across runs
    per_type = defaultdict(lambda: {"classifications": [], "successes": [], "reasoning_samples": []})

    for run_dir in run_dirs:
        report = analyze_model(run_dir)
        for d in report["details"]:
            t = d["type"]
            per_type[t]["classifications"].append(d["classification"])
            per_type[t]["successes"].append(d["success"])
            if d.get("reasoning_text"):
                per_type[t]["reasoning_samples"].append(d["reasoning_text"][:300])

    # Build aggregated report
    aggregated = {
        "model": model_name,
        "n_runs": len(run_dirs),
        "per_type": {},
    }

    for t in sorted(per_type.keys()):
        info = per_type[t]
        n = len(info["classifications"])
        class_counts = Counter(info["classifications"])
        success_count = sum(info["successes"])

        aggregated["per_type"][t] = {
            "n_runs": n,
            "success_count": success_count,
            "success_rate": round(success_count / n, 2) if n else 0,
            "classification_counts": dict(class_counts),
            "dominant_classification": class_counts.most_common(1)[0][0] if class_counts else "unknown",
        }

    return aggregated


def print_aggregated(agg: dict):
    """Print aggregated report."""
    print(f"\n{'='*60}")
    print(f"Aggregated: {agg['model']} ({agg['n_runs']} runs)")
    print(f"{'='*60}")

    for t, info in agg["per_type"].items():
        status = f"{info['success_count']}/{info['n_runs']} pass"
        cls = info["classification_counts"]
        cls_str = ", ".join(f"{v}× {k}" for k, v in sorted(cls.items(), key=lambda x: -x[1]))
        print(f"  {t}: {status} — [{cls_str}]")
    print()


def main():
    parser = argparse.ArgumentParser(description="Analyze reasoning traces")
    parser.add_argument("--model", help="Specific model results dir (single run)")
    parser.add_argument("--aggregate", help="Model name prefix to aggregate (e.g., 'gpt-oss-20b')")
    parser.add_argument("--output", default=None, help="Output JSON path")
    args = parser.parse_args()

    if args.aggregate:
        # Find all run dirs matching the model name
        run_dirs = sorted([
            d for d in RESULTS_DIR.iterdir()
            if d.is_dir() and d.name.startswith(args.aggregate)
        ])
        if not run_dirs:
            print(f"No runs found for '{args.aggregate}' in {RESULTS_DIR}")
            sys.exit(1)

        print(f"Found {len(run_dirs)} runs for {args.aggregate}:")
        for d in run_dirs:
            print(f"  {d.name}")

        if len(run_dirs) == 1:
            # Single run — just analyze normally
            report = analyze_model(run_dirs[0])
            print_report_single(report)
            all_reports = [report]
        else:
            # Multiple runs — aggregate
            agg = aggregate_runs(args.aggregate, run_dirs)
            print_aggregated(agg)
            all_reports = [agg]

            # Also print each individual run
            for d in run_dirs:
                report = analyze_model(d)
                print_report_single(report)
    else:
        if args.model:
            model_dirs = [RESULTS_DIR / args.model]
        else:
            # Group by model prefix (before _run)
            all_dirs = sorted([d for d in RESULTS_DIR.iterdir() if d.is_dir()])
            # Find unique model prefixes
            prefixes = {}
            for d in all_dirs:
                name = d.name
                # Strip _runN suffix
                prefix = re.sub(r'_run\d+$', '', name)
                prefixes.setdefault(prefix, []).append(d)

            all_reports = []
            for prefix, dirs in sorted(prefixes.items()):
                if len(dirs) > 1:
                    agg = aggregate_runs(prefix, dirs)
                    print_aggregated(agg)
                    all_reports.append(agg)
                else:
                    report = analyze_model(dirs[0])
                    print_report_single(report)
                    all_reports.append(report)

            output_path = Path(args.output) if args.output else RESULTS_DIR / "reasoning_analysis.json"
            output_path.write_text(json.dumps(all_reports, indent=2, default=str))
            print(f"Report saved to: {output_path}")
            return

        all_reports = []
        for model_dir in model_dirs:
            if not model_dir.is_dir():
                continue
            report = analyze_model(model_dir)
            all_reports.append(report)
            print_report_single(report)

    # Save report
    output_path = Path(args.output) if args.output else RESULTS_DIR / "reasoning_analysis.json"
    output_path.write_text(json.dumps(all_reports, indent=2, default=str))
    print(f"Report saved to: {output_path}")


def print_report_single(report: dict):
    """Print single-run report."""
    print(f"\n{'='*60}")
    print(f"Model: {report['model']}")
    print(f"{'='*60}")
    print(f"Classification: {report['by_classification']}")
    print()

    for d in report["details"]:
        status = "PASS" if d["success"] else "FAIL"
        cls = d["classification"]
        print(f"  {d['type']}: {status} — {cls}")
        print(f"    Evidence: {d['evidence']}")
        if d.get("reasoning_text"):
            preview = d["reasoning_text"][:150].replace("\n", " ")
            print(f"    Reasoning: {preview}...")
        print()
    print(f"Report saved to: {output_path}")


if __name__ == "__main__":
    main()
