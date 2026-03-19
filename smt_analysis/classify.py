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

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

PROJ_ROOT = Path(__file__).parent.parent.resolve()
RESULTS_DIR = PROJ_ROOT / "smt_analysis" / "results"


def collect_reports(results_dir: Path) -> list[dict]:
    """Collect all report.json files from results directories."""
    reports = []
    for problem_dir in sorted(results_dir.iterdir()):
        if not problem_dir.is_dir():
            continue
        report_file = problem_dir / "report.json"
        if report_file.exists():
            try:
                report = json.loads(report_file.read_text())
                report["_source_dir"] = str(problem_dir)
                reports.append(report)
            except json.JSONDecodeError as e:
                print(f"  WARNING: Invalid JSON in {report_file}: {e}", file=sys.stderr)
    return reports


def extract_quirks(reports: list[dict]) -> list[dict]:
    """Extract all diagnosed quirks from reports."""
    quirks = []
    for report in reports:
        problem_id = report.get("problem_id", "unknown")
        for elem in report.get("essential_elements", []):
            diagnosis = elem.get("diagnosis", {})
            if diagnosis:
                quirks.append({
                    "problem_id": problem_id,
                    "element": elem.get("element", ""),
                    "element_type": elem.get("type", ""),
                    "mechanism": diagnosis.get("mechanism", ""),
                    "explanation": diagnosis.get("explanation", ""),
                    "ghost_var_test": diagnosis.get("ghost_var_test", ""),
                    "confidence": diagnosis.get("confidence", ""),
                    "without_it": elem.get("without_it", {}),
                })
    return quirks


def build_classify_prompt(reports: list[dict], quirks: list[dict]) -> str:
    """Build the classification prompt for Claude."""
    # Summary stats
    total = len(reports)
    solved = sum(1 for r in reports if r.get("solved"))
    with_quirks = sum(1 for r in reports if r.get("essential_elements"))

    # Format all quirks for analysis
    quirk_descriptions = []
    for i, q in enumerate(quirks):
        desc = f"""### Quirk {i+1} (from {q['problem_id']})
**Assertion:** `{q['element']}`
**Type:** {q['element_type']}
**Mechanism:** {q['mechanism']}
**Explanation:** {q['explanation']}
**Ghost var test:** {q['ghost_var_test']}
**Confidence:** {q['confidence']}
**Without it:** {json.dumps(q['without_it'], indent=2)}
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
    parser = argparse.ArgumentParser(description="Classify SMT quirks across all problems")
    parser.add_argument(
        "--reports-dir",
        type=Path,
        default=RESULTS_DIR,
        help="Directory containing per-problem results",
    )
    parser.add_argument(
        "-o", "--output",
        type=Path,
        help="Output file (default: <reports-dir>/quirks_catalog.json)",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=300,
        help="Timeout for Claude classification call (default: 300s)",
    )
    args = parser.parse_args()

    output_file = args.output or (args.reports_dir / "quirks_catalog.json")

    # Collect reports
    print(f"Collecting reports from {args.reports_dir}...")
    reports = collect_reports(args.reports_dir)
    print(f"  Found {len(reports)} reports")

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
    catalog = extract_json_from_response(response)

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
        catalog["per_problem"][pid] = {
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
    print(f"  Categories discovered: {len(qt)}")
    for name, info in qt.items():
        count = info.get("count", "?")
        desc = info.get("description", "")[:80]
        print(f"    {name}: {count} instances — {desc}")
    if summary.get("novel_findings"):
        print(f"  Novel findings: {summary['novel_findings']}")


if __name__ == "__main__":
    main()
