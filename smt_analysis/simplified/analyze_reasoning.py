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
    r"REMOVED.*comment",
    r"the comment (says|indicates)",
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

    # Check if the model read the REMOVED comment
    reads_comment = bool(re.search(r"REMOVED|removed|comment.*(says|indicates|shows)",
                                    reasoning, re.IGNORECASE))

    # Check for actual algebraic steps (e.g., Sum(a[..i+1]) = Sum(a[..i]) + a[i])
    has_algebraic_chain = bool(re.search(
        r"Sum\(.+\)\s*=\s*Sum\(.+\)\s*\+", reasoning)) or bool(re.search(
        r"=.*=.*=", reasoning))

    # Check for SMT-level understanding
    has_smt_understanding = bool(re.search(
        r"Z3|SMT|solver|e-match|trigger|axiom|quantifier.*instantiat",
        reasoning, re.IGNORECASE))

    derivation_score = len(derivation_hits) + (2 if has_algebraic_chain else 0) + (2 if has_smt_understanding else 0)
    pattern_score = len(pattern_hits) + (3 if reads_comment else 0)

    if derivation_score >= 3 and has_algebraic_chain:
        classification = "derivation"
        evidence = f"Algebraic chain found, {len(derivation_hits)} derivation indicators"
    elif derivation_score > pattern_score and derivation_score >= 2:
        classification = "derivation"
        evidence = f"{len(derivation_hits)} derivation indicators vs {len(pattern_hits)} pattern indicators"
    elif reads_comment and pattern_score > derivation_score:
        classification = "comment_reading"
        evidence = f"Reads REMOVED comment, {len(pattern_hits)} pattern indicators"
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
        "reads_comment": reads_comment,
        "has_algebraic_chain": has_algebraic_chain,
        "has_smt_understanding": has_smt_understanding,
        "reasoning_length": len(reasoning),
    }


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


def main():
    parser = argparse.ArgumentParser(description="Analyze reasoning traces")
    parser.add_argument("--model", help="Specific model results dir")
    parser.add_argument("--output", default=None, help="Output JSON path")
    args = parser.parse_args()

    if args.model:
        model_dirs = [RESULTS_DIR / args.model]
    else:
        model_dirs = [d for d in sorted(RESULTS_DIR.iterdir()) if d.is_dir()]

    all_reports = []

    for model_dir in model_dirs:
        if not model_dir.is_dir():
            continue
        report = analyze_model(model_dir)
        all_reports.append(report)

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
                # Show first 150 chars of reasoning
                preview = d["reasoning_text"][:150].replace("\n", " ")
                print(f"    Reasoning: {preview}...")
            print()

    # Save report
    output_path = Path(args.output) if args.output else RESULTS_DIR / "reasoning_analysis.json"
    output_path.write_text(json.dumps(all_reports, indent=2, default=str))
    print(f"Report saved to: {output_path}")


if __name__ == "__main__":
    main()
