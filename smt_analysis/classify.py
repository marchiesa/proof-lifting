#!/usr/bin/env python3
"""
Classification phase — reads all per-problem reports and discovers taxonomy.

Collects all diagnosed quirks across all problems and asks Claude to:
1. Group them by underlying SMT mechanism (not surface syntax)
2. Name each category precisely
3. Count, give representative examples, canonical fix patterns
4. Flag suspect diagnoses

Usage:
    python3 smt_analysis/classify.py
    python3 smt_analysis/classify.py --reports-dir smt_analysis/results
    python3 smt_analysis/classify.py --output quirks_catalog.json
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

PROJ_ROOT = Path(__file__).parent.parent.resolve()
RESULTS_DIR = PROJ_ROOT / "smt_analysis" / "results"


def _normalize_fast_report(raw: dict) -> dict:
    """Convert fast_report.json schema to the common report schema used by this script."""
    problem_id = raw.get("problem", raw.get("problem_id", "unknown"))
    essential_elements = []
    for d in raw.get("diagnoses", []):
        category = d.get("category", "unknown")
        high_level = d.get("high_level", "")
        low_level = d.get("low_level", "")
        pattern = d.get("pattern", d.get("reason", ""))
        confidence = d.get("confidence", "n/a")
        assertion = d.get("assertion", "")
        mechanism = category
        if low_level and low_level != "unknown":
            mechanism = f"{low_level}/{category}"
        explanation = pattern
        if d.get("sub_pattern"):
            explanation = f"{d['sub_pattern']}: {pattern}"
        essential_elements.append(
            {
                "element": assertion,
                "type": "assertion",
                "essential": True,
                "diagnosis": {
                    "mechanism": mechanism,
                    "high_level": high_level,
                    "low_level": low_level,
                    "category": category,
                    "explanation": explanation,
                    "ghost_var_test": "",
                    "confidence": confidence,
                },
                "without_it": {},
            }
        )
    return {
        "problem_id": problem_id,
        "solved": True,
        "attempts": 0,
        "essential_elements": essential_elements,
        "_source_dir": raw.get("_source_dir", ""),
        "_format": "fast",
        "_summary": raw.get("summary", {}),
    }


def collect_reports(results_dir: Path) -> list[dict]:
    """Collect report.json and fast_report.json files from results directories."""
    reports = []
    for problem_dir in sorted(results_dir.iterdir()):
        if not problem_dir.is_dir():
            continue
        report_file = problem_dir / "report.json"
        fast_file = problem_dir / "fast_report.json"
        # Prefer report.json (full analysis); fall back to fast_report.json
        chosen = report_file if report_file.exists() else (fast_file if fast_file.exists() else None)
        if chosen is None:
            continue
        try:
            raw = json.loads(chosen.read_text())
            raw["_source_dir"] = str(problem_dir)
            if chosen.name == "fast_report.json":
                report = _normalize_fast_report(raw)
            else:
                report = raw
            reports.append(report)
        except json.JSONDecodeError as e:
            print(f"  WARNING: Invalid JSON in {chosen}: {e}", file=sys.stderr)
    return reports


def extract_quirks(reports: list[dict]) -> list[dict]:
    """Extract all diagnosed quirks from reports."""
    quirks = []
    for report in reports:
        problem_id = report.get("problem_id", "unknown")
        for elem in report.get("essential_elements", []):
            diagnosis = elem.get("diagnosis", {})
            if diagnosis:
                quirks.append(
                    {
                        "problem_id": problem_id,
                        "element": elem.get("element", ""),
                        "element_type": elem.get("type", ""),
                        "mechanism": diagnosis.get("mechanism", ""),
                        "high_level": diagnosis.get("high_level", ""),
                        "low_level": diagnosis.get("low_level", ""),
                        "category": diagnosis.get("category", ""),
                        "explanation": diagnosis.get("explanation", ""),
                        "ghost_var_test": diagnosis.get("ghost_var_test", ""),
                        "confidence": diagnosis.get("confidence", ""),
                        "without_it": elem.get("without_it", {}),
                    }
                )
    return quirks


_CAT_DESCRIPTIONS = {
    "A1": "Existential witness assertion. The solver needs help instantiating an existential — the assertion provides a concrete witness.",
    "A2": "Predicate/function call assertion. Expands a predicate application so the solver can unfold its definition at that point.",
    "A3": "Function-at-specific-value assertion. Ties a recursive ghost function to a concrete input, avoiding quantifier instantiation failures.",
    "A4": "Universal quantifier assertion. Provides a forall fact the solver cannot derive by E-matching alone.",
    "A5": "Specific-element equality. Pins down the value of a collection element at a particular index to guide unification.",
    "B1": "Sequence slice equality (SMT axiom gap). Boogie's sequence prelude is missing axioms for Seq#Take, Seq#Append or Seq#Drop compositions; the assertion provides the equality via Seq#Equal extensionality.",
    "C1": "Arithmetic / modular identity. The solver's arithmetic reasoning does not propagate a modular or division identity; the assertion states it explicitly.",
    "D1": "Ghost variable equality. Asserts that a ghost variable equals a computed expression, acting as a named intermediate step.",
    "D2": "Bounds assertion. States index/range bounds that the solver cannot derive from the invariant alone.",
    "D3": "Concrete value assertion. Fixes the value of a collection cell (e.g., grid[i][j] == 'W') for the solver.",
    "D4": "Contradiction (assert false). Used in an if-branch to discharge an impossible case; forces Z3 to complete that branch.",
}

_B1_SUBTYPES = {"B1", "B1-take-append", "B1-take-full-length", "B1-seq-extensionality"}


def _normalize_cat(cat: str, mechanism: str) -> str:
    """Merge B1 sub-categories and map legacy mechanism names to categories."""
    if cat in _B1_SUBTYPES or "B1" in cat:
        return "B1"
    # Legacy names from old report.json
    legacy = {
        "structural_requirement": "A-struct",
        "standard accumulator invariant": "A-struct",
        "standard loop bounds invariant": "A-struct",
        "existential witness needed": "A1",
        "missing Take-of-Take axiom": "B1",
        "missing Take-of-full-length axiom": "B1",
        "missing_take_drop_commutation_and_take_of_take_axioms": "B1",
        "universal quantifier proof needed": "A4",
    }
    return legacy.get(cat, cat)


def aggregate_direct(reports: list[dict], quirks: list[dict]) -> dict:
    """Build catalog directly from fast_report categories without calling Claude."""
    from collections import defaultdict

    categories: dict[str, dict] = {}
    high_level_groups: dict[str, list] = defaultdict(list)

    for q in quirks:
        raw_cat = q.get("category") or q.get("mechanism", "unknown")
        cat = _normalize_cat(raw_cat, q.get("mechanism", ""))
        hl = q.get("high_level", "unknown")
        if hl == "unknown" and cat in _CAT_DESCRIPTIONS:
            hl = {
                "A1": "A-structural", "A2": "A-structural", "A3": "A-structural",
                "A4": "A-structural", "A5": "A-structural",
                "B1": "B-missing-axioms",
                "C1": "C-arithmetic",
                "D1": "D-case-analysis", "D2": "D-case-analysis",
                "D3": "D-case-analysis", "D4": "D-case-analysis",
            }.get(cat, hl)
        high_level_groups[hl].append(q)
        if cat not in categories:
            categories[cat] = {
                "count": 0,
                "high_level": hl,
                "low_level": q.get("low_level", ""),
                "description": _CAT_DESCRIPTIONS.get(cat, q.get("explanation", "")),
                "canonical_fix": q.get("element", ""),
                "examples": [],
                "problems": set(),
                "subtypes": defaultdict(int),
            }
        entry = categories[cat]
        entry["count"] += 1
        entry["problems"].add(q["problem_id"])
        if raw_cat != cat:
            entry["subtypes"][raw_cat] += 1
        if len(entry["examples"]) < 3:
            entry["examples"].append(
                {
                    "problem_id": q["problem_id"],
                    "assertion": q["element"],
                    "confidence": q["confidence"],
                }
            )

    # Convert sets to lists for JSON serialisation
    quirk_types = {}
    for name, info in sorted(categories.items(), key=lambda x: -x[1]["count"]):
        entry: dict = {
            "count": info["count"],
            "high_level": info["high_level"],
            "low_level": info["low_level"],
            "description": info["description"],
            "canonical_fix": info["canonical_fix"],
            "examples": info["examples"],
            "problem_count": len(info["problems"]),
        }
        if info["subtypes"]:
            entry["subtypes"] = dict(info["subtypes"])
        quirk_types[name] = entry

    most_common = max(quirk_types, key=lambda k: quirk_types[k]["count"]) if quirk_types else ""
    total_problems = len(reports)
    solved_problems = sum(1 for r in reports if r.get("solved"))

    catalog = {
        "quirk_types": quirk_types,
        "high_level_summary": {
            hl: len(qs) for hl, qs in sorted(high_level_groups.items(), key=lambda x: -len(x[1]))
        },
        "summary": {
            "total_quirks": len(quirks),
            "categories": len(quirk_types),
            "most_common": most_common,
            "total_problems": total_problems,
            "solved_problems": solved_problems,
        },
    }
    return catalog


def build_classify_prompt(reports: list[dict], quirks: list[dict]) -> str:
    """Build the classification prompt for Claude."""
    # Summary stats
    total = len(reports)
    solved = sum(1 for r in reports if r.get("solved"))
    with_quirks = sum(1 for r in reports if r.get("essential_elements"))

    # Format all quirks for analysis
    quirk_descriptions = []
    for i, q in enumerate(quirks):
        desc = f"""### Quirk {i + 1} (from {q["problem_id"]})
**Assertion:** `{q["element"]}`
**Type:** {q["element_type"]}
**Mechanism:** {q["mechanism"]}
**Explanation:** {q["explanation"]}
**Ghost var test:** {q["ghost_var_test"]}
**Confidence:** {q["confidence"]}
**Without it:** {json.dumps(q["without_it"], indent=2)}
"""
        quirk_descriptions.append(desc)

    # Format unsolved problems
    unsolved_notes = []
    for r in reports:
        if not r.get("solved"):
            unsolved_notes.append(
                f"- **{r.get('problem_id')}**: {r.get('notes', 'no notes')}"
            )

    prompt = f"""# SMT Quirk Classification

## Dataset Summary
- Total problems: {total}
- Solved: {solved}
- With diagnosed quirks: {with_quirks}
- Total quirks to classify: {len(quirks)}

## All Diagnosed Quirks

{chr(10).join(quirk_descriptions)}

## Unsolved Problems
{chr(10).join(unsolved_notes) if unsolved_notes else "None"}

## Your Task

Analyze ALL {len(quirks)} quirks above. For each one, you have the assertion that was
needed, what happens without it, and a per-problem diagnosis.

1. **Group these into categories by UNDERLYING MECHANISM** (not by surface syntax).
   Two assertions that look different but work around the same solver limitation
   should be in the same category.

2. **Name each category precisely** (e.g., "sequence slice equality not propagated",
   not "sequence issues").

3. **For each category:**
   - Count of quirks
   - Representative examples (problem_id + assertion)
   - Canonical fix pattern (what assertion pattern works around this)
   - 2-sentence explanation of the solver limitation

4. **Flag any diagnosis that seems wrong** or where the evidence doesn't support
   the claimed mechanism.

5. **Identify patterns across unsolved problems** — are they failing for the same
   reasons as the quirks you categorized?

Output your analysis as JSON with this structure:

```json
{{
  "quirk_types": {{
    "category_name": {{
      "count": N,
      "description": "2-sentence description of the solver limitation",
      "canonical_fix": "assert pattern(...);",
      "examples": [
        {{"problem_id": "...", "assertion": "...", "confidence": "..."}}
      ],
      "subtypes": [
        {{"pattern": "...", "count": N}}
      ]
    }}
  }},
  "suspect_diagnoses": [
    {{"problem_id": "...", "reason": "why this diagnosis seems wrong"}}
  ],
  "unsolved_analysis": "Overall pattern analysis for unsolved problems",
  "summary": {{
    "total_quirks": N,
    "categories": N,
    "most_common": "category_name",
    "novel_findings": "anything unexpected"
  }}
}}
```
"""
    return prompt


def call_claude_classify(prompt: str, timeout: int = 300) -> str | None:
    """Call Claude to classify quirks."""
    try:
        result = subprocess.run(
            [
                "claude",
                "-p",
                "--dangerously-skip-permissions",
                "--no-session-persistence",
            ],
            input=prompt,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=str(PROJ_ROOT),
        )
        return result.stdout
    except subprocess.TimeoutExpired:
        print("ERROR: Claude classification timed out", file=sys.stderr)
        return None
    except Exception as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return None


def extract_json_from_response(response: str) -> dict | None:
    """Extract JSON from Claude's response."""
    # Try to find ```json ... ``` block
    for marker in ["```json", "```"]:
        idx = response.find(marker)
        if idx == -1:
            continue
        start = response.find("\n", idx)
        if start == -1:
            continue
        start += 1
        end = response.find("```", start)
        if end == -1:
            continue
        try:
            return json.loads(response[start:end])
        except json.JSONDecodeError:
            continue

    # Try parsing the whole response as JSON
    try:
        return json.loads(response)
    except json.JSONDecodeError:
        return None


def main():
    parser = argparse.ArgumentParser(
        description="Classify SMT quirks across all problems"
    )
    parser.add_argument(
        "--reports-dir",
        type=Path,
        default=RESULTS_DIR,
        help="Directory containing per-problem results",
    )
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        help="Output file (default: <reports-dir>/quirks_catalog.json)",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=300,
        help="Timeout for Claude classification call (default: 300s)",
    )
    parser.add_argument(
        "--direct",
        action="store_true",
        help="Aggregate fast_report categories directly without calling Claude",
    )
    args = parser.parse_args()

    output_file = args.output or (args.reports_dir / "quirks_catalog.json")

    # Collect reports
    print(f"Collecting reports from {args.reports_dir}...")
    reports = collect_reports(args.reports_dir)
    fast_count = sum(1 for r in reports if r.get("_format") == "fast")
    print(f"  Found {len(reports)} reports ({fast_count} fast_report, {len(reports) - fast_count} report)")

    if not reports:
        print("No reports found. Run quirk_finder.py first.")
        sys.exit(1)

    # Extract quirks
    quirks = extract_quirks(reports)
    print(f"  Extracted {len(quirks)} diagnosed quirks")

    if not quirks:
        print("No diagnosed quirks found in reports.")
        # Still produce a catalog with summary
        catalog = {
            "quirk_types": {},
            "per_problem": {
                r.get("problem_id", "?"): {
                    "solved": r.get("solved", False),
                    "attempts": r.get("attempts", 0),
                    "quirks_found": [],
                }
                for r in reports
            },
            "summary": {
                "total_quirks": 0,
                "categories": 0,
                "total_problems": len(reports),
                "solved_problems": sum(1 for r in reports if r.get("solved")),
            },
        }
        output_file.write_text(json.dumps(catalog, indent=2))
        print(f"  Wrote empty catalog: {output_file}")
        sys.exit(0)

    if args.direct:
        # Aggregate directly from fast_report categories — no Claude call needed
        print("  Aggregating categories directly (--direct mode)...")
        catalog = aggregate_direct(reports, quirks)
    else:
        # Build classification prompt
        prompt = build_classify_prompt(reports, quirks)

        # Save prompt for debugging
        prompt_file = args.reports_dir / "classify_prompt.md"
        prompt_file.write_text(prompt)
        print(f"  Saved classification prompt: {prompt_file}")

        # Call Claude for classification
        print("  Calling Claude for classification...")
        t0 = time.time()
        response = call_claude_classify(prompt, args.timeout)
        elapsed = time.time() - t0
        print(f"  Classification took {elapsed:.0f}s")

        if not response:
            print("ERROR: No response from Claude", file=sys.stderr)
            sys.exit(1)

        # Save raw response
        response_file = args.reports_dir / "classify_response.txt"
        response_file.write_text(response)

        # Parse JSON from response
        catalog = extract_json_from_response(response)  # ty:ignore[invalid-argument-type]

        if not catalog:
            print("WARNING: Could not parse JSON from Claude response", file=sys.stderr)
            print("  Raw response saved to:", response_file)
            # Create a minimal catalog with the raw response
            catalog = {
                "raw_analysis": response,
                "quirk_types": {},
                "summary": {"total_quirks": len(quirks), "parse_error": True},
            }

    # Add per-problem summary
    catalog["per_problem"] = {}
    for report in reports:
        pid = report.get("problem_id", "?")
        catalog["per_problem"][pid] = {  # ty:ignore[invalid-assignment]
            "solved": report.get("solved", False),
            "attempts": report.get("attempts", 0),
            "quirks_found": [
                {
                    "type": e.get("diagnosis", {}).get("mechanism", "unknown"),
                    "assertion": e.get("element", ""),
                }
                for e in report.get("essential_elements", [])
            ],
        }

    # Write catalog
    output_file.write_text(json.dumps(catalog, indent=2))
    print(f"\nQuirks catalog: {output_file}")

    # Print summary
    qt = catalog.get("quirk_types", {})
    summary = catalog.get("summary", {})
    print(f"  Categories discovered: {len(qt)}")  # ty:ignore[invalid-argument-type]
    for name, info in qt.items():
        count = info.get("count", "?")
        desc = info.get("description", "")[:80]
        print(f"    {name}: {count} instances — {desc}")
    if summary.get("novel_findings"):
        print(f"  Novel findings: {summary['novel_findings']}")  # ty:ignore[invalid-argument-type, not-subscriptable]


if __name__ == "__main__":
    main()
