#!/usr/bin/env python3
"""
Summarize ablation results across all problems.

Reads fast_report.json from each problem and produces:
  1. A table of all essential assertions
  2. Grouped by assertion text pattern
  3. Stats for classification planning

Usage:
    python3 smt_analysis/summarize.py
"""

import json
import re
from collections import Counter
from pathlib import Path

RESULTS_DIR = Path(__file__).parent.parent / "smt_analysis" / "results"


def normalize_assertion(expr: str) -> str:
    """Normalize an assertion expression for grouping.

    Replaces variable names with placeholders to group structurally similar assertions.
    """
    # Replace specific variable names with generic ones
    # e.g., "x[..i + 1] == x[..i] + [x[i]]" → "VAR[..IDX + 1] == VAR[..IDX] + [VAR[IDX]]"
    normalized = expr

    # Replace sequence slicing patterns
    normalized = re.sub(r'\b\w+\[\.\.\w+\s*\+\s*1\]', 'SEQ[..IDX + 1]', normalized)
    normalized = re.sub(r'\b\w+\[\.\.\w+\]', 'SEQ[..IDX]', normalized)
    normalized = re.sub(r'\b\w+\[\.\.\|\w+\|\]', 'SEQ[..|SEQ|]', normalized)
    normalized = re.sub(r'\b\w+\[\w+\]', 'SEQ[IDX]', normalized)

    return normalized


def main():
    reports = []
    for report_path in sorted(RESULTS_DIR.glob("*/fast_report.json")):
        report = json.loads(report_path.read_text())
        reports.append(report)

    if not reports:
        print("No fast_report.json files found. Run fast_diagnose.py first.")
        return

    # Collect all essential assertions
    all_essential = []
    problems_with_essential = 0
    problems_without = 0

    for r in reports:
        problem = r.get("problem", "?")
        essential_count = r.get("essential_count", 0)

        if essential_count > 0:
            problems_with_essential += 1
        else:
            problems_without += 1

        # Get essential assertions from ablation results
        ablation_path = RESULTS_DIR / problem / "ablation" / "results.json"
        if ablation_path.exists():
            ablation = json.loads(ablation_path.read_text())
            for a in ablation.get("results", []):
                if a.get("essential"):
                    all_essential.append({
                        "problem": problem,
                        "line": a.get("line", 0),
                        "text": a.get("text", ""),
                        "expr": a.get("expr", ""),
                        "is_equality": a.get("is_equality", False),
                    })

    print(f"{'='*70}")
    print(f"ABLATION SUMMARY")
    print(f"{'='*70}")
    print(f"Problems analyzed: {len(reports)}")
    print(f"  With essential assertions: {problems_with_essential}")
    print(f"  Without (all non-essential): {problems_without}")
    print(f"Total essential assertions: {len(all_essential)}")
    print()

    # Split by type
    equalities = [a for a in all_essential if a["is_equality"]]
    non_equalities = [a for a in all_essential if not a["is_equality"]]

    print(f"Essential equality assertions: {len(equalities)}")
    print(f"Essential non-equality assertions: {len(non_equalities)}")
    print()

    # Group equalities by normalized pattern
    print(f"{'='*70}")
    print(f"EQUALITY ASSERTION PATTERNS (grouped by structure)")
    print(f"{'='*70}")

    pattern_groups = {}
    for a in equalities:
        normalized = normalize_assertion(a["expr"])
        pattern_groups.setdefault(normalized, []).append(a)

    for pattern, items in sorted(pattern_groups.items(), key=lambda x: -len(x[1])):
        print(f"\n  [{len(items):3d}x] {pattern}")
        # Show a few examples
        seen_exprs = set()
        for item in items[:5]:
            if item["expr"] not in seen_exprs:
                print(f"         e.g. {item['problem']}: assert {item['expr']}")
                seen_exprs.add(item["expr"])
            if len(seen_exprs) >= 3:
                break

    # Group non-equalities
    if non_equalities:
        print(f"\n{'='*70}")
        print(f"NON-EQUALITY ASSERTIONS (flagged for review)")
        print(f"{'='*70}")

        for a in non_equalities[:30]:
            print(f"  [{a['problem']}:{a['line']}] {a['text'][:80]}")
        if len(non_equalities) > 30:
            print(f"  ... and {len(non_equalities) - 30} more")

    # Save machine-readable summary
    summary = {
        "total_problems": len(reports),
        "problems_with_essential": problems_with_essential,
        "total_essential": len(all_essential),
        "total_equalities": len(equalities),
        "total_non_equalities": len(non_equalities),
        "patterns": {
            pattern: {
                "count": len(items),
                "examples": [{"problem": a["problem"], "expr": a["expr"]} for a in items[:3]],
            }
            for pattern, items in sorted(pattern_groups.items(), key=lambda x: -len(x[1]))
        },
        "non_equalities": [
            {"problem": a["problem"], "line": a["line"], "text": a["text"]}
            for a in non_equalities
        ],
        "all_essential": all_essential,
    }
    out_path = RESULTS_DIR / "essential_summary.json"
    out_path.write_text(json.dumps(summary, indent=2))
    print(f"\nSaved to: {out_path}")


if __name__ == "__main__":
    main()
