#!/usr/bin/env python3
"""
Prepare Verus benchmark inputs: strip essential assertions from verified code.

Reads verus_quirk_classification.json and produces per-problem inputs:
  - stripped.rs: verified code with ALL essential assertions removed
  - prompt.txt: the prompt to send to the LLM
  - meta.json: problem metadata (original assertions, which were removed)

Usage:
    python3 verus_prepare.py
    python3 verus_prepare.py --names 0000_1013_A 0003_1028_A
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent.resolve()
VERUS_DIR = SCRIPT_DIR.parent / "verus_translation"
PROGRAMS_DIR = VERUS_DIR / "programs"
CLASSIFICATION_FILE = VERUS_DIR / "verus_quirk_classification.json"
OUTPUT_DIR = SCRIPT_DIR / "inputs"

sys.path.insert(0, str(VERUS_DIR))
from verus_classify_quirks import extract_assertions


def strip_essential_assertions(code: str, essentials: list[dict]) -> str:
    """Remove all essential assertions from the source code.

    Handles individual assertions and entire proof blocks.
    Removes lines by commenting them out, then cleans up empty proof blocks.
    """
    lines = code.split("\n")

    # Sort by line descending so removals don't shift later line numbers
    sorted_ess = sorted(essentials, key=lambda a: a["line"], reverse=True)

    for a in sorted_ess:
        start = a["line"] - 1     # 0-indexed
        end = a["end_line"] - 1   # 0-indexed

        if start < 0 or start >= len(lines):
            continue

        for j in range(start, min(end + 1, len(lines))):
            lines[j] = ""

    # Clean up empty proof { } blocks left after removal
    cleaned = []
    i = 0
    while i < len(lines):
        stripped = lines[i].strip()
        # Check for empty proof block: "proof {" followed only by blank/comment lines then "}"
        if stripped.startswith("proof {") or stripped == "proof{":
            block_lines = [i]
            depth = stripped.count("{") - stripped.count("}")
            j = i + 1
            all_empty = True
            while j < len(lines) and depth > 0:
                depth += lines[j].count("{") - lines[j].count("}")
                block_lines.append(j)
                if lines[j].strip() and not lines[j].strip().startswith("//"):
                    all_empty = False
                j += 1
            if all_empty and depth == 0:
                # Skip the entire empty proof block
                i = j
                continue

        cleaned.append(lines[i])
        i += 1

    # Collapse multiple blank lines
    result = []
    prev_blank = False
    for line in cleaned:
        is_blank = line.strip() == ""
        if is_blank and prev_blank:
            continue
        result.append(line)
        prev_blank = is_blank

    return "\n".join(result)


def build_prompt(stripped_code: str, problem_name: str) -> str:
    """Build the full-rewrite prompt for the LLM."""
    return f"""The following Verus program has a correct implementation and specification, but verification fails because some `assert` statements and `proof` blocks are missing. The program verified successfully before these were removed.

RULES — read carefully:
1. Add `assert(...)` statements and `proof {{ }}` blocks to make `verus` verification pass.
2. You may add `proof fn` helper lemmas if needed.
3. You MUST NOT modify ANY existing code. Do not change variable names, assignments, control flow, loop bodies, if/else branches, return statements, or any expression.
4. You MUST NOT modify ANY formal specification. Do not change `requires`, `ensures`, `invariant`, `decreases`, `spec fn` bodies, or function signatures.
5. Any modification to existing code or specifications will be automatically detected and rejected.

Verus hints:
- Use `assert(expr)` for simple assertions
- Use `assert(expr) by {{ ... }}` for assertions needing proof steps
- Use `assert(expr) by(nonlinear_arith) requires ...;` for nonlinear arithmetic
- Use `assert forall|i: int| ... implies ... by {{ ... }};` for quantified assertions
- Use `proof {{ lemma_call(args); }}` to invoke helper lemmas in exec functions
- Use `=~=` for extensional sequence equality (e.g., `assert(s.take(n) =~= s)`)

Return the complete Verus program with your additions inside <VERUS_CODE> tags.

```rust
{stripped_code}
```

<VERUS_CODE>
"""


def build_placeholder_prompt(placeholder_code: str, placeholders: list[dict]) -> str:
    """Build the placeholder prompt for the LLM."""
    placeholder_list = "\n".join(
        f"  PLACEHOLDER_{p['id']}: (line {p['line']})" for p in placeholders
    )
    return f"""The following Verus program has numbered placeholders where `assert` statements or `proof` blocks are needed to make verification pass.

For each placeholder, provide the code that should go there. Output a JSON array with one entry per placeholder:

```json
[
  {{"id": 0, "assertion": "assert(s.take(i + 1).drop_last() =~= s.take(i));"}},
  {{"id": 1, "assertion": "proof {{ sum_append(a, i as int); }}"}}
]
```

RULES:
- Each entry must be valid Verus code (assert statement, proof block, or lemma call)
- Do not include any other code
- Output ONLY the JSON array, nothing else

Placeholders:
{placeholder_list}

```rust
{placeholder_code}
```"""


def make_placeholder_code(code: str, essentials: list[dict]) -> tuple[str, list[dict]]:
    """Replace essential assertions with numbered placeholders."""
    lines = code.split("\n")
    sorted_ess = sorted(essentials, key=lambda a: a["line"])

    placeholders = []
    for pid, a in enumerate(sorted_ess):
        start = a["line"] - 1
        end = a["end_line"] - 1
        if start < 0 or start >= len(lines):
            continue
        indent = len(lines[start]) - len(lines[start].lstrip())
        placeholders.append({
            "id": pid,
            "line": a["line"],
            "end_line": a["end_line"],
            "original_text": a.get("text", ""),
            "indent": indent,
        })

    # Replace in reverse order
    for p in reversed(placeholders):
        start = p["line"] - 1
        end = p["end_line"] - 1
        indent_str = " " * p["indent"]
        for j in range(start, min(end + 1, len(lines))):
            lines[j] = ""
        lines[start] = f"{indent_str}// PLACEHOLDER_{p['id']}: insert assertion here"

    return "\n".join(lines), placeholders


def prepare_problem(problem_name: str, classification: dict) -> dict | None:
    """Prepare benchmark input for one problem."""
    data = classification.get(problem_name)
    if not data or data.get("essential_count", 0) == 0:
        return None

    # Get essentials (excluding lemma calls)
    essentials = [a for a in data.get("essential", [])
                  if a.get("classification", {}).get("category") != "lemma_call"]
    if not essentials:
        return None

    # Find source file
    problem_dir = PROGRAMS_DIR / problem_name
    rs_path = problem_dir / "verified_not_brittle.rs"
    if not rs_path.exists():
        rs_path = problem_dir / "verified.rs"
    if not rs_path.exists():
        return None

    code = rs_path.read_text()

    # Strip all essential assertions
    stripped = strip_essential_assertions(code, essentials)

    # Build prompts
    prompt = build_prompt(stripped, problem_name)

    # Make placeholder version
    placeholder_code, placeholders = make_placeholder_code(code, essentials)
    placeholder_prompt = build_placeholder_prompt(placeholder_code, placeholders)

    # Write outputs
    out_dir = OUTPUT_DIR / problem_name
    out_dir.mkdir(parents=True, exist_ok=True)

    (out_dir / "stripped.rs").write_text(stripped)
    (out_dir / "prompt.txt").write_text(prompt)
    (out_dir / "placeholder.rs").write_text(placeholder_code)
    (out_dir / "placeholder_prompt.txt").write_text(placeholder_prompt)

    meta = {
        "problem": problem_name,
        "source_file": rs_path.name,
        "total_assertions": data.get("total_assertions", 0),
        "essential_count": len(essentials),
        "essential_assertions": [
            {"line": a["line"], "end_line": a["end_line"],
             "text": a["text"][:200], "kind": a.get("kind", ""),
             "classification": a.get("classification", {})}
            for a in essentials
        ],
        "original_code": code[:200] + "...",
        "placeholders": placeholders,
    }
    (out_dir / "meta.json").write_text(json.dumps(meta, indent=2))

    return meta


def main():
    parser = argparse.ArgumentParser(description="Prepare Verus benchmark inputs")
    parser.add_argument("--names", nargs="+", help="Specific problem names")
    args = parser.parse_args()

    classification = json.loads(CLASSIFICATION_FILE.read_text())
    per_problem = classification["per_problem"]

    if args.names:
        problems = args.names
    else:
        # All problems with essential assertions
        problems = sorted(
            name for name, data in per_problem.items()
            if data.get("essential_count", 0) > 0
        )

    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    prepared = 0
    total_essential = 0

    for problem in problems:
        meta = prepare_problem(problem, per_problem)
        if meta:
            prepared += 1
            total_essential += meta["essential_count"]
            print(f"  {problem}: {meta['essential_count']} essential assertions")

    # Write manifest
    manifest = {
        "problems": [p for p in problems if (OUTPUT_DIR / p / "meta.json").exists()],
        "total_problems": prepared,
        "total_essential": total_essential,
    }
    (OUTPUT_DIR / "manifest.json").write_text(json.dumps(manifest, indent=2))

    print(f"\nPrepared {prepared} problems ({total_essential} essential assertions)")
    print(f"Output: {OUTPUT_DIR}")


if __name__ == "__main__":
    main()
