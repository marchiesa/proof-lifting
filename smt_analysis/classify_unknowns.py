#!/usr/bin/env python3
"""
Resolve fast_report unknowns (flagged / unknown-equality) in two stages:

  Stage 1 — Lookup table: match against classification.json by (problem, line) or
            (problem, assertion text).  Fills ~155 of 165 unknowns instantly.

  Stage 2 — Claude: for any that still remain unresolved, build a per-problem prompt
            with the full verified.dfy source and call Claude to classify each one.

Results are written back into each fast_report.json and a fresh quirks_catalog.json
is produced by re-running classify.py --direct.

Usage:
    python3 smt_analysis/classify_unknowns.py
    python3 smt_analysis/classify_unknowns.py --dry-run   # show matches, don't write
    python3 smt_analysis/classify_unknowns.py --claude-only  # skip stage 1
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
CLASSIFICATION_JSON = RESULTS_DIR / "classification.json"

UNKNOWN_CATS = {"flagged", "unknown-equality"}

# Taxonomy reference used in the Claude prompt
TAXONOMY = """
## Taxonomy

Classify each assertion into exactly one category:

| Code | Name | Example |
|------|------|---------|
| A1 | Existential witness | `assert exists c :: P(c);` |
| A2 | Predicate/function call | `assert CellInSquare(i, j, cr, cc, h);` |
| A3 | Function at specific value | `assert a[0] == SeqMin(a);` |
| A4 | Universal quantifier | `assert forall j :: Q(j);` |
| A5 | Specific-element equality | `assert result[|r|] == v;` |
| B1 | Sequence slice equality (SMT axiom gap) | `assert s[..i+1] == s[..i] + [s[i]];` |
| C1 | Arithmetic/modular identity | `assert n == (n/a)*a + n%a;` |
| D1 | Ghost variable equality | `assert ly == gcr - ghalf;` |
| D2 | Bounds assertion | `assert 1 <= r <= n;` |
| D3 | Concrete value assertion | `assert grid[i][j] == 'W';` |
| D4 | Contradiction (assert false) | `assert false;` |

B1 is the main SMT quirk (missing Boogie axioms for Seq#Take/Seq#Append).
The others (A*, C1, D*) are structural helpers or case-analysis steps.
"""


# ---------------------------------------------------------------------------
# Stage 1: lookup from classification.json
# ---------------------------------------------------------------------------

def build_lookup(cls_path: Path) -> tuple[dict, dict]:
    """Return two dicts: by_(problem,line) and by_(problem,text)."""
    data = json.loads(cls_path.read_text())
    by_line: dict[tuple, dict] = {}
    by_text: dict[tuple, dict] = {}
    for item in data:
        pid = item["problem"]
        by_line[(pid, item["line"])] = item
        by_text[(pid, item["text"].strip())] = item
    return by_line, by_text


def resolve_from_lookup(diag: dict, pid: str, by_line: dict, by_text: dict) -> dict | None:
    """Return the classification.json entry matching this diagnosis, or None."""
    key_line = (pid, diag.get("line", -1))
    key_text = (pid, diag.get("assertion", "").strip())
    return by_line.get(key_line) or by_text.get(key_text)


# ---------------------------------------------------------------------------
# Stage 2: Claude analysis
# ---------------------------------------------------------------------------

def build_claude_prompt(pid: str, source: str, unknowns: list[dict]) -> str:
    lines = []
    lines.append(f"# Classify unresolved assertions for problem {pid}\n")
    lines.append(TAXONOMY)
    lines.append("\n## Dafny source (verified.dfy)\n")
    lines.append("```dafny")
    lines.append(source)
    lines.append("```\n")
    lines.append("## Assertions to classify\n")
    for i, u in enumerate(unknowns):
        lines.append(f"### #{i+1}  line={u.get('line')} index={u.get('index')}")
        lines.append(f"```dafny\n{u.get('assertion', '')}\n```")
        if u.get("reason"):
            lines.append(f"Fast-classifier note: {u['reason']}\n")
    lines.append("\n## Required output\n")
    lines.append("Return a JSON array — one object per assertion, in order:\n")
    lines.append("```json")
    lines.append('[{"index": <index>, "category": "<A1|A2|…|D4>", "reasoning": "<1 sentence>"}]')
    lines.append("```")
    lines.append("Output only the JSON, nothing else.")
    return "\n".join(lines)


def call_claude(prompt: str, timeout: int = 180) -> str | None:
    try:
        result = subprocess.run(
            ["claude", "-p", "--dangerously-skip-permissions", "--no-session-persistence"],
            input=prompt,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=str(PROJ_ROOT),
        )
        return result.stdout.strip()
    except subprocess.TimeoutExpired:
        print("  ERROR: Claude timed out", file=sys.stderr)
        return None
    except Exception as e:
        print(f"  ERROR: {e}", file=sys.stderr)
        return None


def extract_json_array(text: str) -> list | None:
    for marker in ["```json", "```"]:
        idx = text.find(marker)
        if idx == -1:
            continue
        start = text.find("\n", idx)
        if start == -1:
            continue
        start += 1
        end = text.find("```", start)
        if end == -1:
            continue
        try:
            return json.loads(text[start:end])
        except json.JSONDecodeError:
            continue
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        return None


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="Resolve fast_report unknowns")
    parser.add_argument("--results-dir", type=Path, default=RESULTS_DIR)
    parser.add_argument("--dry-run", action="store_true", help="Show what would change, don't write")
    parser.add_argument("--claude-only", action="store_true", help="Skip lookup stage, send all to Claude")
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()

    results_dir: Path = args.results_dir
    cls_path = results_dir / "classification.json"

    # Build lookup index
    by_line, by_text = build_lookup(cls_path) if cls_path.exists() else ({}, {})
    print(f"Loaded {len(by_line)} classification entries")

    # Collect all fast_reports
    fast_dirs = [d for d in sorted(results_dir.iterdir()) if d.is_dir() and (d / "fast_report.json").exists()]
    print(f"Found {len(fast_dirs)} fast_report directories\n")

    total_unknowns = 0
    resolved_lookup = 0
    resolved_claude = 0
    still_unknown = 0

    # Track unresolved per problem for Stage 2
    unresolved_by_problem: dict[str, list[dict]] = {}

    # First pass: apply lookup resolutions
    for prob_dir in fast_dirs:
        fr_path = prob_dir / "fast_report.json"
        fr = json.loads(fr_path.read_text())
        pid = fr.get("problem", prob_dir.name)
        changed = False

        for diag in fr.get("diagnoses", []):
            if diag.get("category") not in UNKNOWN_CATS:
                continue
            total_unknowns += 1

            if not args.claude_only:
                match = resolve_from_lookup(diag, pid, by_line, by_text)
                if match:
                    resolved_lookup += 1
                    if not args.dry_run:
                        diag["category"] = match["category"]
                        diag["high_level"] = _high_level(match["category"])
                        diag["low_level"] = _low_level(match["category"])
                        diag["_resolved_by"] = "classification_json"
                    else:
                        print(f"  LOOKUP  {pid} line={diag.get('line')} idx={diag.get('index')} → {match['category']}")
                    changed = True
                    continue

            # Still unresolved — only queue for Claude if not dry-run
            if not args.dry_run:
                if pid not in unresolved_by_problem:
                    unresolved_by_problem[pid] = []
                unresolved_by_problem[pid].append(diag)
            else:
                still_unknown += 1
                print(f"  UNRESOLVED {pid} line={diag.get('line')} idx={diag.get('index')}: {diag.get('assertion','')[:80]}")

        if changed and not args.dry_run:
            fr_path.write_text(json.dumps(fr, indent=2))

    still_unknown = sum(len(v) for v in unresolved_by_problem.values())
    if args.dry_run:
        still_unknown_count = total_unknowns - resolved_lookup
    else:
        still_unknown_count = still_unknown
    print(f"\nStage 1 (lookup): resolved {resolved_lookup}/{total_unknowns} unknowns")
    print(f"Remaining for Claude: {still_unknown_count}\n")
    still_unknown = still_unknown_count

    if still_unknown == 0:
        print("All unknowns resolved. Re-running classify.py --direct...")
        _rebuild_catalog(args)
        return

    # Stage 2: Claude
    for pid, unknowns in sorted(unresolved_by_problem.items()):
        prob_dir = results_dir / pid
        source_file = prob_dir / "verified.dfy"
        if not source_file.exists():
            print(f"  SKIP {pid}: no verified.dfy")
            still_unknown += len(unknowns)
            continue

        source = source_file.read_text()
        prompt = build_claude_prompt(pid, source, unknowns)

        print(f"  Claude: {pid} ({len(unknowns)} unknowns)...")
        t0 = time.time()
        response = call_claude(prompt, args.timeout)
        elapsed = time.time() - t0
        print(f"    {elapsed:.0f}s")

        if not response:
            print(f"    ERROR: no response", file=sys.stderr)
            continue

        parsed = extract_json_array(response)
        if not parsed:
            print(f"    WARNING: could not parse Claude response", file=sys.stderr)
            print(f"    Raw: {response[:200]}", file=sys.stderr)
            continue

        # Apply resolutions back to the fast_report
        fr_path = prob_dir / "fast_report.json"
        fr = json.loads(fr_path.read_text())
        idx_to_cat = {item["index"]: item for item in parsed}

        for diag in fr.get("diagnoses", []):
            if diag.get("category") not in UNKNOWN_CATS:
                continue
            diag_idx = diag.get("index", -1)
            result = idx_to_cat.get(diag_idx)
            if result:
                cat = result["category"]
                diag["category"] = cat
                diag["high_level"] = _high_level(cat)
                diag["low_level"] = _low_level(cat)
                diag["_resolved_by"] = "claude"
                diag["_reasoning"] = result.get("reasoning", "")
                resolved_claude += 1
            else:
                still_unknown += 1

        if not args.dry_run:
            fr_path.write_text(json.dumps(fr, indent=2))

    print(f"\nStage 2 (Claude): resolved {resolved_claude}")
    print(f"Total resolved: {resolved_lookup + resolved_claude}/{total_unknowns}")
    if not args.dry_run:
        _rebuild_catalog(args)


def _high_level(cat: str) -> str:
    if cat == "B1":
        return "B-missing-axioms"
    if cat in ("A1", "A2", "A3", "A4", "A5"):
        return "A-structural"
    if cat == "C1":
        return "C-arithmetic"
    if cat in ("D1", "D2", "D3", "D4"):
        return "D-case-analysis"
    return "unknown"


def _low_level(cat: str) -> str:
    return {
        "A1": "A1-existential-witness",
        "A2": "A2-predicate-call",
        "A3": "A3-function-at-value",
        "A4": "A4-universal",
        "A5": "A5-specific-element",
        "B1": "B1-seq-extensionality",
        "C1": "C1-arithmetic",
        "D1": "D1-ghost-var-eq",
        "D2": "D2-bounds",
        "D3": "D3-concrete-value",
        "D4": "D4-contradiction",
    }.get(cat, "unknown")


def _rebuild_catalog(args):
    print("\nRebuilding quirks_catalog.json...")
    result = subprocess.run(
        [sys.executable, str(PROJ_ROOT / "smt_analysis" / "classify.py"), "--direct",
         "--reports-dir", str(args.results_dir)],
        capture_output=True, text=True, cwd=str(PROJ_ROOT),
    )
    print(result.stdout)
    if result.stderr:
        print(result.stderr, file=sys.stderr)


if __name__ == "__main__":
    main()
