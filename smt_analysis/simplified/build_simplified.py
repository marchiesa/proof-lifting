#!/usr/bin/env python3
from __future__ import annotations
"""
Build simplified minimal examples for each type of essential assertion.

For each quirk type (A2-take-full, B1-trigger-forall, etc.),
creates the smallest possible Dafny program where the same type of
assertion is still essential.

Three-pass pipeline:
  Pass 1: LLM agent creates a minimal example (and verifies it)
  Pass 2: Ablation check — confirm assertion is essential (remove → fail)
  Pass 3: Type check — confirm the quirk type matches the original

Tracks completed types in tracker.json to avoid redundant work.

Usage:
    python3 smt_analysis/simplified/build_simplified.py
    python3 smt_analysis/simplified/build_simplified.py --types A2-take-full A3-take-append
    python3 smt_analysis/simplified/build_simplified.py --max-attempts 5
"""

import argparse
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

PROJ_ROOT = Path(__file__).parent.parent.parent.resolve()
RESULTS_DIR = PROJ_ROOT / "smt_analysis" / "results"
SIMPLIFIED_DIR = PROJ_ROOT / "smt_analysis" / "simplified"
TRACKER_PATH = SIMPLIFIED_DIR / "tracker.json"
DOTNET = os.environ.get("DOTNET8", os.environ.get("DOTNET", "dotnet"))
DAFNY_DLL = os.environ.get("DAFNY_DLL",
    str(PROJ_ROOT / "dafny-source" / "Binaries" / "Dafny.dll"))

# ---------------------------------------------------------------------------
# Assertion type grouping
# ---------------------------------------------------------------------------

# Known quirk types with regex patterns for matching
QUIRK_TYPES = {
    "A2-take-full": {
        "pattern": r"assert\s+\w+\[\.\.[\|]\w+[\|]\]\s*==\s*\w+\s*;",
        "description": "Sequence take-full: a[..|a|] == a",
        "example_hint": "A loop that processes a sequence prefix a[..i] and needs a[..|a|] == a after the loop.",
    },
    "A3-take-append": {
        "pattern": r"assert\s+\w+\[\.\..*\+\s*1\]\s*==\s*\w+\[\.\..*\]\s*\+\s*\[",
        "description": "Sequence take-append: a[..i+1] == a[..i] + [a[i]]",
        "example_hint": "A loop that builds up a result from a sequence prefix, needing a[..i+1] == a[..i] + [a[i]] in the loop body.",
    },
    "A1-take-take": {
        "pattern": r"assert\s+\w+\[\.\..*\]\[\.\..*\]\s*==",
        "description": "Nested take: a[..i+1][..i] == a[..i]",
        "example_hint": "A recursive function over a[..i] where unfolding produces a[..i+1][..i].",
    },
    "B1-trigger-forall": {
        "pattern": r"assert\s+[A-Z]\w+\(",
        "description": "Predicate not evaluated: assert P(a, b, c)",
        "example_hint": "A ghost predicate P(x,y) that Z3 won't evaluate at specific arguments without an explicit assert.",
    },
    "B2-trigger-existential": {
        "pattern": r"assert\s+(exists|.*==.*FriendSum|.*ValidCombo)",
        "description": "Missing witness for existential quantifier",
        "example_hint": "A postcondition with 'exists k :: ...' where Z3 needs a ground term as witness.",
    },
    "B1-trigger-forall-unfolding": {
        "pattern": r"assert\s+[A-Z]\w+\(.*\)\s*==",
        "description": "Function not unfolded: assert F(x) == y",
        "example_hint": "A recursive ghost function where Z3 won't unfold it at specific args.",
    },
    "D1-other-nla": {
        "pattern": r"assert\s+.*[%/\*].*",
        "description": "NLA: modulo, division, or multiplication hint",
        "example_hint": "An assertion involving n % k or n / k that Z3's NLA solver can't derive.",
    },
    "C1-brittle": {
        "pattern": r"assert\s+\w+\s*==\s*\w+\s*[-+]\s*\w+\s*;",
        "description": "Equality not propagated from assignments",
        "example_hint": "Ghost variables assigned from other variables, where Z3 won't substitute and simplify.",
    },
    "D1-other-case": {
        "pattern": r"assert\s+false\s*;",
        "description": "Unreachable branch: assert false",
        "example_hint": "A case split where one branch is unreachable but Z3 can't derive the contradiction.",
    },
}


def classify_assertion(text: str) -> str | None:
    """Classify an assertion by its text pattern. Returns type name or None."""
    for type_name, info in QUIRK_TYPES.items():
        if re.search(info["pattern"], text):
            return type_name
    return None


def get_all_essential_assertions() -> list[dict]:
    """Collect all essential assertions from ablation results."""
    verified_path = RESULTS_DIR / "verified_problems.txt"
    if not verified_path.exists():
        return []
    verified = set(verified_path.read_text().split())

    assertions = []
    for d in sorted(RESULTS_DIR.iterdir()):
        if not d.is_dir() or d.name not in verified:
            continue
        r = d / "ablation" / "results.json"
        if not r.exists():
            continue
        data = json.loads(r.read_text())
        for a in data["results"]:
            if a.get("essential"):
                a["problem"] = d.name
                a["type"] = classify_assertion(a.get("text", ""))
                assertions.append(a)
    return assertions


def load_tracker() -> dict:
    """Load tracker of completed types."""
    if TRACKER_PATH.exists():
        return json.loads(TRACKER_PATH.read_text())
    return {"completed": {}, "failed": {}}


def save_tracker(tracker: dict):
    """Save tracker."""
    TRACKER_PATH.write_text(json.dumps(tracker, indent=2))


# ---------------------------------------------------------------------------
# Pass 1: Create minimal example
# ---------------------------------------------------------------------------

PROMPT_TEMPLATE = """Create the SMALLEST possible Dafny program that demonstrates this SMT solver quirk:

Type: {type_name}
Description: {description}

Original assertion from a real verified program:
```
{original_assertion}
```

From this original program context (showing only the relevant method):
```dafny
{code_context}
```

REQUIREMENTS:
1. The program must VERIFY with `dafny verify` (0 errors)
2. It must contain ONE assert statement of the same type as above
3. Removing that assert must cause verification to FAIL
4. Keep the program as SHORT as possible — ideally under 30 lines
5. Use simple variable names, minimal specs
6. The program must be self-contained (no imports)

{example_hint}

Return ONLY the Dafny code, no explanations.

```dafny
"""


def get_code_context(problem: str, line: int) -> str:
    """Get the source code context around an assertion."""
    for name in ["verified_inlined.dfy", "verified.dfy"]:
        path = RESULTS_DIR / problem / name
        if path.exists():
            lines = path.read_text().split("\n")
            start = max(0, line - 15)
            end = min(len(lines), line + 15)
            return "\n".join(lines[start:end])
    return ""


def call_claude(prompt: str) -> str:
    """Call Claude via the claude CLI. Returns the response text."""
    result = subprocess.run(
        ["claude", "-p", prompt, "--output-format", "text", "--max-turns", "1"],
        capture_output=True, text=True, timeout=300,
    )
    return result.stdout.strip()


def extract_dafny_code(response: str) -> str | None:
    """Extract Dafny code from response."""
    for pattern in [r'```dafny\s*(.*?)\s*```', r'```\s*(.*?)\s*```']:
        m = re.search(pattern, response, re.DOTALL)
        if m:
            return m.group(1).strip()
    # If no code blocks, assume the whole response is code
    if "method " in response or "function " in response:
        return response.strip()
    return None


def verify_dafny(code: str, tmp_dir: Path) -> tuple[bool, str]:
    """Run dafny verify. Returns (success, output)."""
    dfy = tmp_dir / "example.dfy"
    dfy.write_text(code)
    try:
        result = subprocess.run(
            [DOTNET, DAFNY_DLL, "verify", str(dfy),
             "--verification-time-limit", "30"],
            capture_output=True, text=True, timeout=60,
        )
        output = result.stdout + "\n" + result.stderr
    except (subprocess.TimeoutExpired, FileNotFoundError) as e:
        output = str(e)
    return "0 errors" in output, output.strip()


def pass1_create(type_name: str, assertion: dict,
                 max_attempts: int = 3) -> tuple[str | None, str]:
    """Pass 1: Create minimal example. Returns (code, status)."""
    info = QUIRK_TYPES.get(type_name, {})
    context = get_code_context(assertion["problem"], assertion.get("line", 0))

    prompt = PROMPT_TEMPLATE.format(
        type_name=type_name,
        description=info.get("description", type_name),
        original_assertion=assertion.get("text", ""),
        code_context=context,
        example_hint=info.get("example_hint", ""),
    )

    tmp_dir = SIMPLIFIED_DIR / "tmp" / type_name
    tmp_dir.mkdir(parents=True, exist_ok=True)

    for attempt in range(1, max_attempts + 1):
        print(f"    Pass 1 attempt {attempt}...")
        response = call_claude(prompt)
        code = extract_dafny_code(response)

        if not code:
            print(f"    Could not extract code from response")
            prompt = f"Your previous response didn't contain valid Dafny code. Try again.\n\n{prompt}"
            continue

        success, output = verify_dafny(code, tmp_dir)
        if success:
            print(f"    Verified on attempt {attempt}")
            return code, "ok"
        else:
            errors = [l for l in output.split("\n") if "Error" in l or "error" in l]
            error_msg = "\n".join(errors[:5])
            print(f"    Verification failed: {error_msg[:100]}")
            prompt = f"Your code failed verification:\n{error_msg}\n\nFix it and try again. Remember: the program must verify WITH the assert.\n\n{prompt}"

    return None, "pass1_failed"


# ---------------------------------------------------------------------------
# Pass 2: Ablation check
# ---------------------------------------------------------------------------

def pass2_ablation(code: str, type_name: str) -> tuple[bool, str]:
    """Pass 2: Remove the assert and check verification fails."""
    tmp_dir = SIMPLIFIED_DIR / "tmp" / type_name
    tmp_dir.mkdir(parents=True, exist_ok=True)

    lines = code.split("\n")
    # Find assert lines
    assert_lines = []
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith("assert ") and not stripped.startswith("assert false"):
            assert_lines.append(i)

    if not assert_lines:
        # Also look for assert false if that's the type
        for i, line in enumerate(lines):
            if line.strip().startswith("assert "):
                assert_lines.append(i)

    if not assert_lines:
        return False, "no assert found"

    # Try removing each assert individually
    for ai in assert_lines:
        stripped_lines = lines.copy()
        # Find the end of this assert (including by-block)
        end = ai
        while end < len(stripped_lines) and ";" not in stripped_lines[end]:
            end += 1
        # Check for by block
        if end + 1 < len(stripped_lines) and stripped_lines[end + 1].strip().startswith("by"):
            depth = 0
            end += 1
            while end < len(stripped_lines):
                depth += stripped_lines[end].count("{") - stripped_lines[end].count("}")
                if depth <= 0 and "{" in stripped_lines[end]:
                    break
                end += 1

        for j in range(ai, end + 1):
            stripped_lines[j] = "// REMOVED"

        stripped_code = "\n".join(stripped_lines)
        success, output = verify_dafny(stripped_code, tmp_dir)

        if not success:
            # Good — removing the assert causes failure
            return True, f"assert at line {ai + 1} is essential"

    return False, "all asserts are non-essential"


# ---------------------------------------------------------------------------
# Pass 3: Type check
# ---------------------------------------------------------------------------

def pass3_type_check(code: str, type_name: str, original_text: str) -> tuple[bool, str]:
    """Pass 3: Check the simplified example has at least one assert of the target type."""
    found_types = []
    for line in code.split("\n"):
        stripped = line.strip()
        if stripped.startswith("assert "):
            detected = classify_assertion(stripped)
            if detected:
                found_types.append(detected)
            if detected == type_name:
                return True, f"type matches: {type_name}"

    if found_types:
        return False, f"type mismatch: expected {type_name}, found {found_types}"

    # Loose checks for types that patterns may miss
    if type_name.startswith("A") and type_name[1:2].isdigit() and "[.." in code:
        return True, f"sequence operations present (loose match for {type_name})"

    if type_name == "B1-trigger-forall":
        for line in code.split("\n"):
            if line.strip().startswith("assert ") and re.search(r"[A-Z]\w+\(", line):
                return True, "predicate call in assert"

    return False, f"could not confirm type {type_name}"


# ---------------------------------------------------------------------------
# Main loop
# ---------------------------------------------------------------------------

def process_type(type_name: str, assertions: list[dict],
                 tracker: dict, max_attempts: int = 3) -> bool:
    """Process one quirk type. Returns True if successful."""
    if type_name in tracker["completed"]:
        print(f"  SKIP {type_name}: already completed")
        return True

    # Pick the simplest assertion of this type (shortest text)
    assertion = min(assertions, key=lambda a: len(a.get("text", "")))

    print(f"\n  Processing: {type_name}")
    print(f"  Representative: {assertion['problem']} — {assertion.get('text', '')[:60]}")

    for retry in range(max_attempts):
        if retry > 0:
            print(f"  Retry {retry + 1}...")

        # Pass 1: Create
        code, status = pass1_create(type_name, assertion, max_attempts=3)
        if not code:
            print(f"  Pass 1 FAILED: {status}")
            continue

        # Pass 2: Ablation
        essential, msg = pass2_ablation(code, type_name)
        if not essential:
            print(f"  Pass 2 FAILED: {msg}")
            continue

        # Pass 3: Type check
        type_ok, msg = pass3_type_check(code, type_name, assertion.get("text", ""))
        if not type_ok:
            print(f"  Pass 3 FAILED: {msg}")
            continue

        # All passes succeeded
        out_dir = SIMPLIFIED_DIR / "examples" / type_name
        out_dir.mkdir(parents=True, exist_ok=True)

        (out_dir / "example.dfy").write_text(code)

        # Create stripped version
        lines = code.split("\n")
        for i, line in enumerate(lines):
            if line.strip().startswith("assert "):
                lines[i] = "// TODO: add assertion here"
                # Handle multiline
                while i < len(lines) - 1 and ";" not in lines[i]:
                    i += 1
                    lines[i] = "// TODO: add assertion here"
                break
        (out_dir / "stripped.dfy").write_text("\n".join(lines))

        meta = {
            "type": type_name,
            "description": QUIRK_TYPES.get(type_name, {}).get("description", ""),
            "source_problem": assertion["problem"],
            "source_assertion": assertion.get("text", ""),
            "source_line": assertion.get("line", 0),
            "lines_of_code": len([l for l in code.split("\n") if l.strip()]),
            "pass2_result": msg,
            "pass3_result": msg,
        }
        (out_dir / "meta.json").write_text(json.dumps(meta, indent=2))

        tracker["completed"][type_name] = {
            "problem": assertion["problem"],
            "assertion": assertion.get("text", ""),
            "lines": meta["lines_of_code"],
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
        }
        save_tracker(tracker)

        print(f"  SUCCESS: {meta['lines_of_code']} lines")
        return True

    tracker["failed"][type_name] = {
        "problem": assertion["problem"],
        "assertion": assertion.get("text", ""),
        "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
    }
    save_tracker(tracker)
    print(f"  FAILED after {max_attempts} retries")
    return False


def main():
    parser = argparse.ArgumentParser(description="Build simplified quirk examples")
    parser.add_argument("--types", nargs="+", help="Specific types to process")
    parser.add_argument("--max-attempts", type=int, default=3)
    parser.add_argument("--list", action="store_true", help="List types and counts, then exit")
    args = parser.parse_args()

    SIMPLIFIED_DIR.mkdir(exist_ok=True)

    # Collect and group assertions by type
    all_assertions = get_all_essential_assertions()
    by_type = {}
    untyped = []
    for a in all_assertions:
        t = a.get("type")
        if t:
            by_type.setdefault(t, []).append(a)
        else:
            untyped.append(a)

    print(f"Essential assertions: {len(all_assertions)}")
    print(f"Typed: {sum(len(v) for v in by_type.values())} across {len(by_type)} types")
    print(f"Untyped: {len(untyped)}")
    print()

    for t, asserts in sorted(by_type.items(), key=lambda x: -len(x[1])):
        print(f"  {t}: {len(asserts)} assertions from {len(set(a['problem'] for a in asserts))} problems")

    if args.list:
        return

    tracker = load_tracker()
    print(f"\nAlready completed: {len(tracker['completed'])} types")
    print()

    types_to_process = args.types if args.types else sorted(by_type.keys())

    successes = 0
    failures = 0
    for type_name in types_to_process:
        if type_name not in by_type:
            print(f"  SKIP {type_name}: no assertions of this type")
            continue
        ok = process_type(type_name, by_type[type_name], tracker, args.max_attempts)
        if ok:
            successes += 1
        else:
            failures += 1

    print(f"\nDone: {successes} succeeded, {failures} failed")
    print(f"Tracker: {TRACKER_PATH}")


if __name__ == "__main__":
    main()
