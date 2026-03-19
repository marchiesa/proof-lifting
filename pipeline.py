#!/usr/bin/env python3
"""
Pipeline: Codeforces -> Dafny benchmark problems.

Steps per problem:
1. LLM produces Dafny method SIGNATURE (no body, no spec)
2. Script RUNS Python solution on test inputs -> derives I/O pairs.
   LLM translates I/O pairs into tests.dfy (typed Dafny calls).
3. LLM produces method BODY. Script tests with `dafny run --no-verify`. Fix loop.
4. LLM produces formal spec (NON-GHOST, bounded quantifiers).
   Script generates NEGATIVE tests by modifying outputs.
   If a negative test fails (spec accepts modified output), spawn separate Claude
   to diagnose: valid alternative solution OR spec bug.
   Fix loop.

Each step is tested before moving to the next.
Timeout: 5 minutes per problem. Failures go to queue/.
"""

import json
import os
import random
import subprocess
import sys
import tempfile
import time
import shutil
from pathlib import Path

DAFNY = "/opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll"
MAX_RETRIES = 3
TIMEOUT_SECONDS = 3600
DATASET_DIR = Path("dataset")
QUEUE_DIR = Path("queue")
CODEFORCES_DIR = Path("codeforces_data")


def load_data():
    with open(CODEFORCES_DIR / "problems.json") as f:
        problems = {p["id"]: p for p in json.load(f)}
    with open(CODEFORCES_DIR / "python_submissions.json") as f:
        submissions = json.load(f)
    joined = []
    for sub in submissions:
        pid = sub["problem_id"]
        if pid in problems:
            p = problems[pid]
            joined.append({
                "id": pid,
                "title": p["title"],
                "description": p["description"],
                "input_format": p["input_format"],
                "output_format": p["output_format"],
                "examples": p["examples"],
                "official_tests": p["official_tests"],
                "rating": p["rating"],
                "tags": p["tags"],
                "note": p.get("note", ""),
                "python_code": sub["source"],
                "python_lang": sub["language"],
            })
    return joined


def call_claude(prompt, timeout=120, label=""):
    """Call claude CLI in print mode, piping prompt via stdin."""
    t0 = time.time()
    try:
        result = subprocess.run(
            ["claude", "-p", "--dangerously-skip-permissions", "--no-session-persistence",
             "--verbose", "--debug-file", "/tmp/claude_debug.log"],
            input=prompt,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd="/tmp",
        )
        elapsed = time.time() - t0
        print(f"    [timing] claude call{f' ({label})' if label else ''}: {elapsed:.0f}s, prompt {len(prompt)} chars, output {len(result.stdout)} chars")
        return result.stdout
    except subprocess.TimeoutExpired:
        return None
    except Exception as e:
        print(f"  Error calling claude: {e}")
        return None


def extract_dafny_block(output):
    """Extract first ```dafny ... ``` or ``` ... ``` code block from output."""
    for marker in ["```dafny", "```"]:
        idx = output.find(marker)
        if idx == -1:
            continue
        start = output.find("\n", idx)
        if start == -1:
            continue
        start += 1
        end = output.find("```", start)
        if end == -1:
            continue
        return output[start:end].strip()
    return None


def extract_json_block(output):
    """Extract first ```json ... ``` or ``` ... ``` code block from output."""
    for marker in ["```json", "```"]:
        idx = output.find(marker)
        if idx == -1:
            continue
        start = output.find("\n", idx)
        if start == -1:
            continue
        start += 1
        end = output.find("```", start)
        if end == -1:
            continue
        try:
            return json.loads(output[start:end].strip())
        except json.JSONDecodeError:
            continue
    # Try parsing the whole output as JSON
    try:
        return json.loads(output.strip())
    except json.JSONDecodeError:
        return None


def run_dafny(filepath, timeout=60):
    """Run dafny run --no-verify. Returns (success, output)."""
    cmd = f"{DAFNY} run --no-verify --allow-warnings {filepath}"
    try:
        result = subprocess.run(
            cmd, shell=True, capture_output=True, text=True, timeout=timeout
        )
        combined = result.stdout + result.stderr
        success = result.returncode == 0
        return success, combined
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT"
    except Exception as e:
        return False, f"ERROR: {e}"


def py2_to_py3(code):
    """Convert Python 2 competitive-programming code to Python 3.

    Handles: print statements, input()/raw_input(), xrange, map/filter/zip
    iterators, fractions.gcd, dict methods, long literals, has_key, basestring.
    """
    import re

    # ── 1. input() semantics ─────────────────────────────────────
    # py2 input() does eval() (returns int for numeric input).
    # py3 input() always returns str.
    # Wrap bare input() → int(input()), but NOT raw_input() or input().split().
    # Must run BEFORE raw_input → input conversion.
    code = re.sub(
        r'(?<!raw_)(?<!int\()(?<!str\()(?<!float\()(?<!eval\()\binput\(\)',
        'int(input())',
        code,
    )
    # Undo wrapping when followed by . (e.g., input().split(), input().strip())
    code = re.sub(r'int\(input\(\)\)\.', 'input().', code)
    # Don't double-wrap
    code = code.replace('int(int(input()))', 'int(input())')

    # ── 2. raw_input → input ─────────────────────────────────────
    code = code.replace("raw_input()", "input()")
    code = code.replace("raw_input", "input")
    # Clean up `input = input` (from `input = raw_input`)
    code = re.sub(r'^\s*input\s*=\s*input\s*$', '', code, flags=re.MULTILINE)

    # ── 3. xrange → range ────────────────────────────────────────
    code = re.sub(r'\bxrange\b', 'range', code)
    # Clean up `range = range` (from `range = xrange`)
    code = re.sub(r'^\s*range\s*=\s*range\s*$', '', code, flags=re.MULTILINE)

    # ── 4. print statement → print function ──────────────────────
    # Handle print at start of line (with optional indent)
    code = re.sub(r'^([ \t]*)print\s+(?!\()(.+)$',
                  r'\1print(\2)', code, flags=re.MULTILINE)
    # Handle inline print after colon: `if x: print "y"`, `else: print "y"`
    code = re.sub(r'(:\s*)print\s+(?!\()(.+)$',
                  lambda m: f"{m.group(1)}print({m.group(2)})",
                  code, flags=re.MULTILINE)

    # ── 5. map/filter assigned to variable → list() ──────────────
    # py2 map() returns list; py3 returns iterator (breaks len/index/sort).
    # Only wrap single-variable assignments (unpacking works on iterators).
    code = re.sub(r'^(\s*\w+\s*=\s*)map\((.+)\)\s*$',
                  r'\1list(map(\2))', code, flags=re.MULTILINE)
    code = re.sub(r'^(\s*\w+\s*=\s*)filter\((.+)\)\s*$',
                  r'\1list(filter(\2))', code, flags=re.MULTILINE)

    # ── 6. fractions.gcd → math.gcd (removed in py3.5) ──────────
    code = code.replace("from fractions import gcd", "from math import gcd")

    # ── 7. Other py2 → py3 fixes ─────────────────────────────────
    code = re.sub(r'(\w+)\.has_key\((.+?)\)', r'\2 in \1', code)
    code = re.sub(r'(\d+)L\b', r'\1', code)
    code = code.replace(".iteritems()", ".items()")
    code = code.replace(".itervalues()", ".values()")
    code = code.replace(".iterkeys()", ".keys()")
    code = code.replace("basestring", "str")

    return code


def _py2_to_py3_intdiv(code):
    """Additional pass: convert / to // for integer division (py2 semantic)."""
    import re
    code = py2_to_py3(code)
    # Replace / with // outside of strings and comments.
    # Only replace standalone / (not // or /=).
    lines = code.split('\n')
    result = []
    for line in lines:
        # Skip comment-only lines
        stripped = line.lstrip()
        if stripped.startswith('#'):
            result.append(line)
            continue
        # Split line into code and comment parts
        in_str = None
        code_end = len(line)
        for i, ch in enumerate(line):
            if ch in ('"', "'") and (i == 0 or line[i-1] != '\\'):
                if in_str is None:
                    in_str = ch
                elif ch == in_str:
                    in_str = None
            elif ch == '#' and in_str is None:
                code_end = i
                break
        code_part = line[:code_end]
        comment_part = line[code_end:]
        # Replace / with // in code part, avoiding strings
        new_code = []
        in_str = None
        i = 0
        while i < len(code_part):
            ch = code_part[i]
            if ch in ('"', "'") and (i == 0 or code_part[i-1] != '\\'):
                if in_str is None:
                    in_str = ch
                elif ch == in_str:
                    in_str = None
                new_code.append(ch)
            elif ch == '/' and in_str is None:
                # Check it's not already // or /=
                if i + 1 < len(code_part) and code_part[i+1] in ('/', '='):
                    new_code.append(ch)
                elif i > 0 and code_part[i-1] == '/':
                    new_code.append(ch)
                else:
                    new_code.append('//')
                    i += 1
                    continue
            else:
                new_code.append(ch)
            i += 1
        result.append(''.join(new_code) + comment_part)
    return '\n'.join(result)


def _run_code(code, test_input, timeout=10):
    """Run a single code string on input. Returns output string or None."""
    with tempfile.NamedTemporaryFile(mode="w", suffix=".py", delete=False) as f:
        f.write(code)
        tmpfile = f.name
    try:
        normalized_input = test_input.replace("\r\n", "\n").strip() + "\n"
        result = subprocess.run(
            [sys.executable, tmpfile],
            input=normalized_input,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        if result.returncode == 0:
            return result.stdout.strip()
    except (subprocess.TimeoutExpired, Exception):
        pass
    finally:
        os.unlink(tmpfile)
    return None


def _pick_best_variant(python_code, examples):
    """Pick the code variant that produces correct output on examples.

    Returns the best code variant string.
    """
    variants = [python_code, py2_to_py3(python_code), _py2_to_py3_intdiv(python_code)]

    # If we have examples with expected output, validate against them
    validated_examples = [(ex["input"].strip(), ex["output"].strip())
                          for ex in examples
                          if ex.get("input", "").strip() and ex.get("output", "").strip()]

    if validated_examples:
        for variant in variants:
            all_match = True
            for inp, expected in validated_examples[:3]:  # test first 3 examples
                out = _run_code(variant, inp)
                if out is None or out.strip() != expected:
                    all_match = False
                    break
            if all_match:
                return variant

    # No examples or none matched — return first variant that runs at all
    if validated_examples:
        inp = validated_examples[0][0]
    else:
        inp = "1\n"
    for variant in variants:
        out = _run_code(variant, inp)
        if out is not None:
            return variant

    return python_code  # fallback


def run_python_on_input(python_code, test_input, timeout=10):
    """Run the Python solution on a test input. Returns output string or None."""
    return _run_code(python_code, test_input, timeout)


def generate_random_inputs(problem, existing_inputs, count=10):
    """Ask Claude to generate random test inputs matching the problem's input format.

    Returns list of input strings.
    """
    examples_str = ""
    for ex in problem.get("examples", []):
        inp = ex.get("input", "").strip()
        if inp:
            examples_str += f"```\n{inp}\n```\n"

    prompt = f"""Generate {count} random test inputs for this competitive programming problem.
Keep values SMALL (numbers ≤ 50, strings ≤ 10 chars, arrays ≤ 10 elements) so the solution runs fast.

## Problem description:
{problem['description']}

## Input format:
{problem.get('input_format', 'See description.')}

## Example inputs:
{examples_str}

Return ONLY a JSON array of strings, where each string is one complete test input.
Example format: ["1\\n3 5", "2\\n1 2\\n3 4"]
No explanation, just the JSON array."""

    output = call_claude(prompt, timeout=60, label="generate_inputs")
    if not output:
        return []

    parsed = extract_json_block(output)
    if isinstance(parsed, list):
        return [s for s in parsed if isinstance(s, str)]

    # Try parsing the whole output as JSON
    try:
        parsed = json.loads(output.strip())
        if isinstance(parsed, list):
            return [s for s in parsed if isinstance(s, str)]
    except json.JSONDecodeError:
        pass

    return []


def derive_test_pairs(problem):
    """Run Python solution on all test inputs to derive I/O pairs.

    Returns list of {"input": str, "output": str} where output is from
    actually running the code (ground truth).
    """
    # Pick the best code variant (original, py2→py3, or py2→py3+intdiv)
    examples = problem.get("examples", [])
    python_code = _pick_best_variant(problem["python_code"], examples)
    pairs = []
    seen_inputs = set()

    # Gather all test inputs (examples + official tests)
    all_tests = []
    for ex in examples:
        all_tests.append(ex)
    for test in problem.get("official_tests", []):
        all_tests.append(test)

    for test in all_tests:
        inp = test.get("input", "").replace("\r\n", "\n").strip()
        if not inp or inp in seen_inputs:
            continue
        seen_inputs.add(inp)

        output = _run_code(python_code, inp)
        if output is not None:
            pairs.append({"input": inp, "output": output})

        if len(pairs) >= 20:  # cap at 20 test cases
            break

    # If we don't have enough pairs, generate random inputs
    if len(pairs) < 5:
        print(f"  Only {len(pairs)} I/O pairs from examples, generating random inputs...")
        random_inputs = generate_random_inputs(problem, [p["input"] for p in pairs])
        for inp in random_inputs:
            inp = inp.replace("\r\n", "\n").strip()
            if not inp or inp in seen_inputs:
                continue
            seen_inputs.add(inp)

            output = _run_code(python_code, inp)
            if output is not None:
                pairs.append({"input": inp, "output": output})

            if len(pairs) >= 20:
                break

    return pairs


def generate_negative_outputs(pairs):
    """Generate negative test cases by modifying outputs.

    For each positive pair, create a modified output that should be rejected.
    Returns list of {"input": str, "output": str, "original_output": str}.
    """
    negatives = []
    for pair in pairs[:10]:  # cap at 10 negatives
        original = pair["output"]
        modified = _modify_output(original)
        if modified != original:
            negatives.append({
                "input": pair["input"],
                "output": modified,
                "original_output": original,
            })
    return negatives


def _modify_output(output):
    """Modify an output string to create a negative test case."""
    # Try to parse as number and perturb
    try:
        val = int(output.strip())
        return str(val + 1)
    except ValueError:
        pass

    try:
        val = float(output.strip())
        return str(val + 0.5)
    except ValueError:
        pass

    # For Yes/No type outputs, flip them
    stripped = output.strip()
    if stripped.lower() in ("yes", "no"):
        return "No" if stripped.lower() == "yes" else "Yes"
    if stripped.lower() in ("true", "false"):
        return "False" if stripped.lower() == "true" else "True"

    # For multi-line or multi-value outputs, try modifying first value
    lines = output.strip().split("\n")
    if len(lines) >= 1:
        parts = lines[0].split()
        if parts:
            try:
                val = int(parts[0])
                parts[0] = str(val + 1)
                lines[0] = " ".join(parts)
                return "\n".join(lines)
            except ValueError:
                pass

    # Fallback: append something
    return output.strip() + " WRONG"


def format_io_pairs(pairs, max_pairs=20):
    """Format derived I/O pairs as readable string."""
    lines = []
    for i, pair in enumerate(pairs[:max_pairs]):
        lines.append(f"Test {i+1}:")
        lines.append(f"  Input:  {pair['input']}")
        lines.append(f"  Output: {pair['output']}")
    return "\n".join(lines)


# ─── STEP 1: SIGNATURE ──────────────────────────────────────────────

def step1_signature(problem):
    """Ask LLM for just the Dafny method signature."""
    prompt = f"""I have a Codeforces problem. I need you to produce ONLY a Dafny method signature.

## Problem: {problem['title']}

{problem['description']}

Input format: {problem['input_format']}
Output format: {problem['output_format']}

## Python solution (for reference):
```python
{problem['python_code']}
```

## What I need:

Produce ONLY the Dafny method signature. No body, no spec, no invariants.

The signature must:
- Use clean typed parameters: seq<int>, int, bool, string, seq<seq<int>>, etc.
- NOT use stdin/stdout parsing
- Transform the text I/O into proper typed parameters and return values
- Include `returns` clause

Example of what I want (for a two-sum problem):
```dafny
method TwoSum(nums: seq<int>, target: int) returns (i: int, j: int)
```

Output ONLY the signature inside a ```dafny block. Nothing else.
"""
    output = call_claude(prompt, label="step1_signature")
    if output is None:
        return None
    return extract_dafny_block(output)


# ─── STEP 2: TESTS (derived from running Python) ────────────────────

def step2_tests(problem, signature, io_pairs):
    """Ask LLM to translate derived I/O pairs into tests.dfy."""
    pairs_str = format_io_pairs(io_pairs)

    prompt = f"""I have a Dafny method signature and input/output pairs derived from running the original code. Write a tests.dfy file.

## Method signature:
```dafny
{signature}
```

## Problem: {problem['title']}
{problem['description'][:500]}

## Input/output pairs (derived by running the original Python solution):
{pairs_str}

## What I need:

Write a complete `tests.dfy` file with:
1. The method signature with an EMPTY body (just `return` default values to make it compile)
2. A `Main` method that:
   - Calls the method with concrete inputs derived from the test cases above
   - Uses `expect` (NOT assert) to check the outputs match expected values
   - Prints "All tests passed" at the end

Transform the text I/O into typed Dafny calls. For example if the input is "5\\n3 1 4 1 5" and the method takes `a: seq<int>`, the call should be `var result := MyMethod([3, 1, 4, 1, 5]);`

Include ALL the test cases provided above. These are ground-truth pairs from running the real solution, so they are correct.

This file will be tested with `dafny run --no-verify`. If there are errors, I will provide them and you'll fix it.

Output the complete file in a ```dafny block.
"""
    output = call_claude(prompt, timeout=600, label="step2_tests")
    if output is None:
        print("  [debug] step2: claude returned None (timeout?)")
        return None
    block = extract_dafny_block(output)
    if block is None:
        print(f"  [debug] step2: no code block. Output starts with: {output[:300]}")
    return block


# ─── STEP 3: IMPLEMENTATION ─────────────────────────────────────────

def step3_implementation(problem, signature, tests_content):
    """Ask LLM to produce the complete file: method impl + all tests."""
    prompt = f"""I have a Dafny test file with a stub method. Replace the stub with a real implementation.

## Test file (method has stub body + Main with tests):
```dafny
{tests_content}
```

## Python solution to translate:
```python
{problem['python_code']}
```

## What I need:

Output the COMPLETE file with:
1. The method with a real implementation body (translate the Python algorithm)
2. ALL existing tests in Main() — keep them exactly as-is

Rules:
- Do NOT add loop invariants, ghost variables, or assertions
- Do NOT add requires/ensures clauses (no spec yet)
- Just translate the algorithm faithfully
- Keep the exact same method signature
- Keep ALL tests unchanged

Output the COMPLETE file in a ```dafny block.
"""
    output = call_claude(prompt, label="step3_impl")
    if output is None:
        return None
    return extract_dafny_block(output)


def step3_fix(code_content, tests_content, error_output):
    """Fix implementation based on dafny errors."""
    prompt = f"""This Dafny code has errors when run with `dafny run --no-verify`. Fix it.

## Current code (in tests.dfy, which includes the method + Main):
```dafny
{tests_content}
```

## Error output:
```
{error_output[-2000:]}
```

## Rules:
- Fix the errors so `dafny run --no-verify` succeeds and prints "All tests passed"
- Do NOT add loop invariants, ghost variables, assertions, requires, or ensures
- Just fix the implementation and/or the test expectations

Output the COMPLETE fixed tests.dfy file in a ```dafny block.
"""
    output = call_claude(prompt, label="step3_fix")
    if output is None:
        return None
    return extract_dafny_block(output)


# ─── STEP 4: FORMAL SPEC ────────────────────────────────────────────

def _step4a_prompt(problem, working_code, rejection_feedback=None):
    """Build the step4a prompt, optionally including rejection feedback."""
    rejection_section = ""
    if rejection_feedback:
        rejection_section = f"""

## PREVIOUS ATTEMPT REJECTED

Your previous spec was rejected because it encodes the algorithm's shortcut formula
rather than the problem's operational definition. Here is the specific feedback:

{rejection_feedback}

You MUST fix this. Define the operations/conditions from the problem statement as
predicates, then use them in the ensures clause. Do NOT encode the answer formula.
"""

    return f"""I have working Dafny code. Add a formal specification that is COMPILABLE (testable at runtime).

## Working code:
```dafny
{working_code}
```

## Problem: {problem['title']}
{problem['description']}
{rejection_section}
## What I need:

Add a formal specification to this code. The spec must formalize the PROBLEM STATEMENT,
not the algorithm. Do NOT just restate what the code computes — capture the mathematical
meaning of what it means for the output to be correct according to the problem.

CRITICAL RULE: The spec must define correctness INDEPENDENTLY of the algorithm. Someone
reading only the spec (without the method body) should understand WHAT the correct answer
is from the problem statement alone. The spec predicates/functions must model the problem's
STRUCTURE (operations, constraints, relationships), not the shortcut that makes the
algorithm efficient.

BAD example — encoding the algorithm's answer:
  // Problem: "can we transform x to y via take/move operations?"
  predicate CanTransform(x: seq<int>, y: seq<int>) {{
    Sum(y) <= Sum(x)  // This is the THEOREM, not the DEFINITION
  }}

GOOD example — modeling the problem's operations:
  // Problem: "can we transform x to y via take/move operations?"
  predicate LegalStep(before: seq<int>, after: seq<int>) {{
    // Define what one take or move operation does...
  }}
  predicate CanTransform(x: seq<int>, y: seq<int>, steps: nat) {{
    // Can we reach y from x in 'steps' legal operations?
  }}
  ensures result == exists steps | 0 <= steps <= BOUND :: CanTransform(x, y, steps)

The ensures clause must reference predicates that MODEL THE PROBLEM, not predicates
that ENCODE THE ANSWER.

Rules:
1. Write predicate(s) and/or function(s) that capture correctness.
   - Do NOT use the `ghost` keyword — everything must be compilable.
   - All quantifiers must have explicit bounds so Dafny can enumerate them at runtime.
     Use the filter syntax: `forall i | 0 <= i < n :: P` and `exists x | lo <= x <= hi :: P`

2. For existentials over complex types (seq, set, map) that Dafny cannot enumerate:
   Use explicit index-based constructions instead. For example, instead of:
     `exists z: seq<int> :: |z| == |x| && ValidStep(x, z) && Reachable(z, y, steps - 1)`
   Write:
     `(exists i | 0 <= i < |x| :: x[i] > 0 && Reachable(x[i := x[i] - 1], y, steps - 1))`
   The key: replace `exists composite_value :: property(composite_value)` with
   `exists indices :: property(construct_from(indices))`.

3. When defining recursive functions/predicates over sequences, prefer SLICE-BASED recursion
   (recurse on a sub-sequence) over INDEX-PARAMETER recursion.
   GOOD (slice-based) — recurse on the sequence itself:
     function Sum(a: seq<int>): int
       decreases |a|
       if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
   BAD (index-based) — pass an extra index parameter:
     function Sum(a: seq<int>, k: nat): int
       if k == 0 then 0 else Sum(a, k-1) + a[k-1]
   The slice-based style is the natural mathematical definition and is preferred.

4. Add `requires` and `ensures` clauses to the method using those predicates.

5. Do NOT modify the method body. Do NOT add loop invariants, ghost variables, or assertions.

6. For any recursive predicate that searches a bounded space (like reachability in N steps),
   add a bound parameter, e.g.: `predicate ReachableIn(x: seq<int>, y: seq<int>, steps: nat)`
   with `exists steps | 0 <= steps <= BOUND :: ReachableIn(x, y, steps)`.

Output the COMPLETE file (spec predicates + method with requires/ensures) in a ```dafny block.
"""


def step4a_validate_spec(problem, spec_code):
    """Validate that a generated spec models the problem structure, not the algorithm's shortcut.
    Returns (is_valid, feedback) where feedback explains the issue if invalid."""
    prompt = f"""You are a formal verification reviewer. Check whether this Dafny specification
correctly formalizes the PROBLEM STATEMENT or whether it takes a shortcut by encoding
the algorithm's answer formula directly.

## Problem: {problem['title']}
{problem['description']}

## Specification:
```dafny
{spec_code}
```

## What to check:

1. Does the `ensures` clause reference predicates that model the problem's STRUCTURE
   (operations, constraints, relationships from the problem statement)?
   Or does it directly encode the ANSWER (a shortcut formula equivalent to what the
   algorithm computes)?

2. Look at the predicates/functions defined. Do they define the concepts from the
   problem statement (legal moves, valid configurations, reachability, etc.)?
   Or do they just compute the same thing as the method body?

3. Specifically: if the problem describes operations/transformations/reachability,
   the spec MUST define what a legal operation is and assert reachability.
   It must NOT just assert a numeric condition (like Sum(y) <= Sum(x)) that happens
   to be equivalent.

4. If the spec defines operational predicates (like LegalStep) but then the ensures
   clause doesn't actually USE them (uses a shortcut instead), that's ALSO wrong.

Reply with EXACTLY one of:
- "VALID" if the spec correctly models the problem structure
- "SHORTCUT: <explanation>" if the spec encodes the answer instead of the problem

Be strict. If in doubt, say SHORTCUT.
"""
    output = call_claude(prompt, timeout=120, label="step4a_validate")
    if output is None:
        return True, None  # Can't validate, assume ok
    output = output.strip()
    if output.upper().startswith("VALID"):
        return True, None
    # Extract feedback after "SHORTCUT:"
    if "SHORTCUT" in output.upper():
        feedback = output.split(":", 1)[-1].strip() if ":" in output else output
        return False, feedback
    # Ambiguous — assume valid
    return True, None


def step4a_testable_spec(problem, working_code):
    """Step 4a: Generate a TESTABLE formal spec (compilable, bounded, with slicing).
    This is tested first. The ghost version is derived from it in step 4b.
    Includes validation that rejects shortcut specs."""
    MAX_ATTEMPTS = 3
    rejection_feedback = None

    for attempt in range(MAX_ATTEMPTS):
        prompt = _step4a_prompt(problem, working_code, rejection_feedback)
        output = call_claude(prompt, timeout=600, label=f"step4a_testable_spec{'_retry' + str(attempt) if attempt > 0 else ''}")
        if output is None:
            print("  [debug] step4a: claude returned None (timeout?)")
            return None
        block = extract_dafny_block(output)
        if block is None:
            print(f"  [debug] step4a: no code block found. Output starts with: {output[:300]}")
            return None

        # Validate the spec isn't a shortcut
        is_valid, feedback = step4a_validate_spec(problem, block)
        if is_valid:
            if attempt > 0:
                print(f"  [debug] step4a: spec accepted after {attempt + 1} attempts")
            return block

        print(f"  [debug] step4a: SHORTCUT DETECTED (attempt {attempt + 1}/{MAX_ATTEMPTS}): {feedback[:200]}")
        rejection_feedback = feedback

    # All attempts produced shortcut specs — return last one anyway
    print(f"  [debug] step4a: WARNING — all {MAX_ATTEMPTS} attempts produced shortcut specs, using last one")
    return block


def _strip_main(code):
    """Remove Main() method from code to reduce size for LLM prompts."""
    idx = code.find("method Main()")
    if idx == -1:
        idx = code.find("method Main ()")
    if idx > 0:
        return code[:idx].rstrip()
    return code


def step4b_ghost_spec(problem, testable_spec_code):
    """Step 4b: Generalize testable spec to ghost spec with MINIMAL changes.
    The ghost spec is derived from the tested-and-validated testable spec."""
    spec_only = _strip_main(testable_spec_code)

    prompt = f"""Generalize this Dafny spec to a ghost (verification-only) version with MINIMAL changes.

## STRICT RULES — the output must be structurally identical to the input except for these changes:

1. Add `ghost` before every `predicate` and `function` declaration.
   `predicate Foo(...)` → `ghost predicate Foo(...)`
   `function Bar(...)` → `ghost function Bar(...)`

2. Generalize bounded quantifiers to unbounded where the bound was artificial:
   - `forall i | 0 <= i < n :: P` → `forall i :: 0 <= i < n ==> P`  (move filter to guard)
   - `exists x | 0 <= x <= BOUND :: P` → `exists x :: P`  (remove artificial bound)
   - `exists steps | 0 <= steps <= BOUND :: P` → `exists steps: nat :: P`
   Keep bounds that are INHERENT to the problem (e.g., `0 <= i < |array|` stays bounded).
   Only remove bounds that were added purely for compilability (e.g., `<= 10`, `<= 20`).

3. For index-based constructions that were used to avoid `exists` over complex types,
   generalize back to an existential over the complex type:
   - `exists i | 0 <= i < |x| :: x[i] > 0 && Reachable(x[i := x[i] - 1], y, steps - 1)`
   → `exists z: seq<int> :: |z| == |x| && ValidStep(x, z) && Reachable(z, y, steps - 1)`
   Only do this if the original clearly was encoding "there exists a sequence/set/map".
   If the index-based form IS the natural mathematical statement, keep it.

4. Do NOT:
   - Rename any predicate, function, method, or variable
   - Change any method signatures (parameters, return types, requires, ensures)
   - Rewrite logic that is already correct
   - Add new predicates/functions
   - Remove or restructure any code

The goal: someone diffing the testable spec against your output should see only `ghost` additions,
bound removals, and (where applicable) existential generalizations. Nothing else.

```dafny
{spec_only}
```

Output the modified code in a ```dafny block.
"""
    output = call_claude(prompt, timeout=120, label="step4b_ghost")
    if output is None:
        return None
    return extract_dafny_block(output)


def step4c_spec_tests(testable_spec_code, io_pairs, negative_pairs, problem):
    """Step 4c: Build tests for the testable spec + implementation tests."""
    pos_str = format_io_pairs(io_pairs[:10])
    neg_lines = []
    for i, neg in enumerate(negative_pairs[:10]):
        neg_lines.append(f"Negative {i+1}:")
        neg_lines.append(f"  Input:  {neg['input']}")
        neg_lines.append(f"  Wrong output: {neg['output']}")
        neg_lines.append(f"  Correct output: {neg['original_output']}")
    neg_str = "\n".join(neg_lines)

    prompt = f"""I have Dafny code with a testable (non-ghost) spec, and I have test pairs.
Write a complete tests.dfy that tests BOTH the implementation AND the spec predicates.

## Code with testable spec:
```dafny
{testable_spec_code}
```

## Problem: {problem['title']}
{problem['description'][:300]}

## POSITIVE test pairs (derived by running the original code — these are correct):
{pos_str}

## NEGATIVE test pairs (output was modified — spec should REJECT these):
{neg_str}

## What I need:

Write a COMPLETE tests.dfy file that includes:
1. All the predicates/functions from the testable spec above
2. The method with its full implementation and requires/ensures
3. A Main method with:

   a. SPEC POSITIVE tests: For EACH positive test pair, call the TOP-LEVEL ensures predicate
      with the test input and correct output. This is a 1-to-1 mapping from the test pairs.
      If the ensures says `ensures result == F(x, y)`, test `expect F(x, y) == expected_output`.
      If the ensures says `ensures P(x, result)`, test `expect P(x, expected_output)`.
      IMPORTANT: The spec may use bounded existential quantifiers that are expensive to evaluate.
      For spec tests, use SMALL inputs only: sequences length 1-3, values 0-5.
      Scale down the test pairs to small equivalent cases if needed.
      You may skip a test pair if it would be too large for bounded quantifier enumeration,
      but include at least 5 spec positive tests.
      Do NOT test helper predicates — ONLY the top-level predicate from the `ensures` clause.
      Use `expect MyTopLevelPredicate(input, correct_output), "spec positive N";`

   b. SPEC NEGATIVE tests: For EACH negative test pair, call the SAME top-level ensures predicate
      with the test input and WRONG output. Again, 1-to-1 from the negative pairs.
      Same rule: SMALL inputs only (length 1-3, values 0-5). Scale down if needed.
      You may skip a test pair if it would be too large, but include at least 5 spec negative tests.
      Do NOT test helper predicates — ONLY the top-level predicate from the `ensures` clause.
      Use `expect !MyTopLevelPredicate(input, wrong_output), "spec negative N";`

   c. IMPLEMENTATION tests: call the method and check it returns the correct output.
      These CAN use the full-size test pairs above (the method is fast).
      Use `expect result == expected, "impl test N failed";`

   d. Print "All tests passed" at the end

The predicates are NOT ghost, so they can be called at runtime.
This will be tested with `dafny run --no-verify`. If there are errors, I will show them and ask you to fix.

Output the COMPLETE file in a ```dafny block.
"""
    output = call_claude(prompt, timeout=600, label="step4c_tests")
    if output is None:
        return None
    return extract_dafny_block(output)


def step4_diagnose_negative(spec_code, test_input, modified_output, original_output, problem):
    """Spawn a separate Claude to diagnose: is the modified output a valid alternative, or is the spec wrong?

    Returns "alternative" if the modified output is actually valid, "spec_bug" if the spec is wrong.
    """
    prompt = f"""I have a Dafny formal specification for a Codeforces problem, and a test case where the spec
ACCEPTS an output that I expected it to REJECT. I need you to determine why.

## Problem: {problem['title']}
{problem['description'][:500]}

## The formal spec:
```dafny
{spec_code}
```

## Test case:
- Input: {test_input}
- Original correct output: {original_output}
- Modified output (expected to be rejected): {modified_output}
- But the spec ACCEPTED the modified output

## Question:
Is this because:
(A) The modified output is actually a VALID ALTERNATIVE solution to the problem (the problem has multiple correct answers), OR
(B) The formal spec has a BUG — it's too permissive and accepts wrong answers

Reason step by step, then answer with EXACTLY one of:
- "ALTERNATIVE" if the modified output is genuinely valid
- "SPEC_BUG" if the spec is too permissive

Then, if it's a SPEC_BUG, suggest how to fix the spec predicate to reject this case.

Output your answer as:
```json
{{"verdict": "ALTERNATIVE" or "SPEC_BUG", "reasoning": "...", "fix_suggestion": "..." or null}}
```
"""
    output = call_claude(prompt, timeout=60)
    if output is None:
        return "unknown", None
    result = extract_json_block(output)
    if result and isinstance(result, dict):
        verdict = result.get("verdict", "unknown").lower()
        fix = result.get("fix_suggestion")
        if "alternative" in verdict:
            return "alternative", fix
        elif "spec_bug" in verdict:
            return "spec_bug", fix
    return "unknown", None


def _diagnose_error(error_output):
    """Classify the Dafny error and suggest a fix strategy."""
    err = error_output.lower()
    suggestions = []

    if "quantifiers in non-ghost contexts must be compilable" in err:
        suggestions.append(
            "COMPILABILITY ERROR: A quantifier uses a type that Dafny cannot enumerate at runtime "
            "(e.g. `exists z: seq<int> | ...`). Dafny cannot enumerate sequences/sets/maps even "
            "with a size bound. Fix: inline the construction — replace `exists composite :: P(composite)` "
            "with `exists indices :: P(construct(indices))`. For example, instead of "
            "`exists z: seq<int> :: ValidStep(x, z) && ...`, expand ValidStep to construct z "
            "directly: `exists i | 0 <= i < |x| :: x[i] > 0 && Reachable(x[i := x[i]-1], y, n-1)`."
        )
    if "ambiguous use of && and ||" in err:
        suggestions.append(
            "PARSE ERROR: Dafny requires parentheses to disambiguate && and ||. "
            "Wrap the || branches in parentheses."
        )
    if "expectation violation" in err:
        suggestions.append(
            "TEST FAILURE: An expect statement failed. Check if the spec predicate is computing "
            "the wrong result for the test input. For spec positive tests, the predicate must "
            "return true. For spec negative tests, it must return false. If a bounded existential "
            "search is too shallow (not enough steps), try increasing the bound or using smaller "
            "test inputs."
        )
    if "timeout" in err or "TIMEOUT" in error_output:
        suggestions.append(
            "TIMEOUT: The spec predicate is too expensive to evaluate at runtime. "
            "Use smaller test inputs (length 1-2, values 0-3). Reduce existential bounds "
            "(e.g. steps <= 5 instead of steps <= 20). Avoid testing cases that require deep search."
        )
    if "resolution/type error" in err or "type mismatch" in err:
        suggestions.append(
            "TYPE ERROR: Check that predicate arguments match their declarations. "
            "Ensure requires clauses are satisfied at every call site."
        )

    if not suggestions:
        suggestions.append("Check the error message carefully and fix the specific issue reported.")

    return "\n".join(f"- {s}" for s in suggestions)


def step4_fix(tests_content, error_output):
    """Fix spec or spec tests based on errors, with diagnosis."""
    diagnosis = _diagnose_error(error_output)

    prompt = f"""This Dafny file has errors when run with `dafny run --no-verify`. Fix it.

## Current file:
```dafny
{tests_content}
```

## Error output:
```
{error_output[-2000:]}
```

## Diagnosis and suggestions:
{diagnosis}

## Rules:
- Fix so `dafny run --no-verify` succeeds and prints "All tests passed"
- All predicates/functions must be NON-GHOST (no `ghost` keyword)
- All quantifiers must be COMPILABLE. Dafny can enumerate integers with bounds, but CANNOT
  enumerate complex types (seq, set, map) even with size bounds. If you have
  `exists z: seq<T> | |z| <= N :: P(z)`, this will NOT compile. Instead, inline the
  construction: replace it with `exists indices :: P(construct(indices))`.
- Do NOT add loop invariants, ghost variables, or assertions
- Do NOT remove spec predicates — fix them

Output the COMPLETE fixed file in a ```dafny block.
"""
    output = call_claude(prompt)
    if output is None:
        return None
    return extract_dafny_block(output)


def step4_fix_spec(spec_code, problem, fix_suggestion, failing_case):
    """Fix the spec itself based on a diagnosed bug."""
    prompt = f"""The formal spec for this Dafny code has a bug — it accepts wrong answers.

## Current spec code:
```dafny
{spec_code}
```

## Problem: {problem['title']}
{problem['description'][:500]}

## Failing case:
- Input: {failing_case['input']}
- Wrong output accepted: {failing_case['output']}
- Correct output: {failing_case['original_output']}

## Suggested fix:
{fix_suggestion}

## Rules:
- Fix the spec predicates/functions so they correctly REJECT the wrong output
- MUST remain `predicate` or `function`, NOT `ghost predicate`
- All quantifiers MUST be bounded
- Do NOT modify the method body
- Do NOT add loop invariants, ghost variables, or assertions

Output the COMPLETE fixed file in a ```dafny block.
"""
    output = call_claude(prompt)
    if output is None:
        return None
    return extract_dafny_block(output)


# ─── MAIN PIPELINE ──────────────────────────────────────────────────

def process_problem(problem, idx):
    """Process one problem through all 4 steps."""
    pid = problem["id"].replace("/", "_")
    title = problem["title"]
    print(f"\n{'='*60}")
    print(f"[{idx}] {pid}: {title} (rating {problem['rating']})")
    print(f"{'='*60}")

    start_time = time.time()
    problem_dir = DATASET_DIR / f"{idx:04d}_{pid}"
    problem_dir.mkdir(parents=True, exist_ok=True)

    # Save metadata
    with open(problem_dir / "problem.json", "w") as f:
        json.dump({
            "id": problem["id"], "title": title,
            "rating": problem["rating"], "tags": problem["tags"],
            "description": problem["description"],
        }, f, indent=2)
    with open(problem_dir / "solution.py", "w") as f:
        f.write(problem["python_code"])

    def timed_out():
        if time.time() - start_time > TIMEOUT_SECONDS:
            print(f"  TIMEOUT after {time.time() - start_time:.0f}s")
            return True
        return False

    def retry_step(step_fn, step_name, *args, **kwargs):
        """Retry a step function until it returns non-None or time runs out."""
        attempt = 0
        while not timed_out():
            attempt += 1
            result = step_fn(*args, **kwargs)
            if result:
                return result
            print(f"  {step_name}: attempt {attempt} failed, retrying...")
        return None

    # ── STEP 0: Derive I/O pairs by running Python ──────────────
    print("  Step 0: Running Python solution on test inputs...")
    io_pairs = derive_test_pairs(problem)
    if len(io_pairs) < 2:
        print(f"  FAILED: Only {len(io_pairs)} I/O pairs derived (need ≥ 2)")
        return False
    print(f"  Derived {len(io_pairs)} I/O pairs")

    # Save derived pairs
    with open(problem_dir / "io_pairs.json", "w") as f:
        json.dump(io_pairs, f, indent=2)

    # Generate negative test cases by modifying outputs
    negative_pairs = generate_negative_outputs(io_pairs)
    print(f"  Generated {len(negative_pairs)} negative test cases")

    with open(problem_dir / "negative_pairs.json", "w") as f:
        json.dump(negative_pairs, f, indent=2)

    if timed_out():
        return False

    # ── STEP 1: Signature ────────────────────────────────────────
    print("  Step 1: Getting signature...")
    signature = retry_step(step1_signature, "step1", problem)
    if not signature:
        print("  FAILED: No signature")
        return False
    print(f"  Signature: {signature.strip()}")
    with open(problem_dir / "signature.txt", "w") as f:
        f.write(signature)

    # ── STEP 2: Tests (from derived I/O pairs) ───────────────────
    print("  Step 2: Getting tests from derived I/O pairs...")
    tests_content = retry_step(step2_tests, "step2", problem, signature, io_pairs)
    if not tests_content:
        print("  FAILED: No tests")
        return False
    with open(problem_dir / "tests.dfy", "w") as f:
        f.write(tests_content)

    # Check tests compile (with empty body they should just return defaults)
    success, output = run_dafny(problem_dir / "tests.dfy")
    if not success:
        print(f"  Tests don't compile yet (expected, will fix with implementation)")
    if timed_out():
        return False

    # ── STEP 3: Implementation ───────────────────────────────────
    print("  Step 3: Getting implementation...")
    impl_result = retry_step(step3_implementation, "step3", problem, signature, tests_content)
    if not impl_result:
        print("  FAILED: No implementation")
        return False
    tests_content = impl_result

    with open(problem_dir / "tests.dfy", "w") as f:
        f.write(tests_content)

    # Test implementation — retry until passing or timeout
    while not timed_out():
        print(f"  Testing implementation...")
        success, output = run_dafny(problem_dir / "tests.dfy")

        if success and "All tests passed" in output:
            print(f"  Implementation works!")
            break

        print(f"  Failed. Fixing...")
        fixed = retry_step(step3_fix, "step3_fix", tests_content, tests_content, output)
        if fixed:
            tests_content = fixed
            with open(problem_dir / "tests.dfy", "w") as f:
                f.write(tests_content)
        else:
            print(f"  FAILED: Could not fix implementation")
            return False
    else:
        return False

    # Save working implementation separately
    with open(problem_dir / "working_impl.dfy", "w") as f:
        f.write(tests_content)
    if timed_out():
        return False

    # ── STEP 4a: Testable spec (compilable, bounded) ───────────
    print("  Step 4a: Getting testable formal spec...")
    testable_spec = retry_step(step4a_testable_spec, "step4a", problem, tests_content)
    if not testable_spec:
        print("  FAILED: No testable spec")
        return False

    # ── STEP 4c: Spec tests (small inputs) + impl tests ────────
    print("  Step 4c: Getting spec + impl tests...")
    spec_tests = retry_step(step4c_spec_tests, "step4c", testable_spec, io_pairs, negative_pairs, problem)
    if spec_tests:
        tests_content = spec_tests
        with open(problem_dir / "tests.dfy", "w") as f:
            f.write(tests_content)

    # Test spec — retry with fixes until passing or timeout
    while not timed_out():
        print(f"  Testing spec...")
        success, output = run_dafny(problem_dir / "tests.dfy")

        if success and "All tests passed" in output:
            print(f"  Spec works!")
            break

        # Check if the failure is a negative test that passed (spec too permissive)
        if "spec should reject" in output and "expectation violation" in output.lower():
            for neg in negative_pairs:
                print(f"  Diagnosing: spec accepted modified output '{neg['output']}' for input '{neg['input'][:80]}'")
                verdict, fix = step4_diagnose_negative(
                    testable_spec, neg["input"], neg["output"],
                    neg["original_output"], problem
                )
                if verdict == "alternative":
                    print(f"    -> Valid alternative solution, removing this negative test")
                    negative_pairs = [n for n in negative_pairs if n != neg]
                elif verdict == "spec_bug":
                    print(f"    -> Spec bug detected, fixing spec...")
                    fixed_spec = step4_fix_spec(testable_spec, problem, fix, neg)
                    if fixed_spec:
                        testable_spec = fixed_spec
                    break

            # Regenerate tests with updated spec / negative pairs
            spec_tests = retry_step(step4c_spec_tests, "step4c_regen", testable_spec, io_pairs, negative_pairs, problem)
            if spec_tests:
                tests_content = spec_tests
                with open(problem_dir / "tests.dfy", "w") as f:
                    f.write(tests_content)
            continue

        print(f"  Failed. Fixing...")
        fixed = retry_step(step4_fix, "step4_fix", tests_content, output)
        if fixed:
            tests_content = fixed
            with open(problem_dir / "tests.dfy", "w") as f:
                f.write(tests_content)
        else:
            print(f"  FAILED: Could not fix spec")
            return False
    else:
        return False

    # ── STEP 4b: Derive ghost spec from tested testable spec ───
    print("  Step 4b: Deriving ghost spec from testable spec...")
    ghost_spec = retry_step(step4b_ghost_spec, "step4b", problem, testable_spec)
    if not ghost_spec:
        print("  FAILED: No ghost spec")
        return False
    with open(problem_dir / "task.dfy", "w") as f:
        f.write(ghost_spec)

    # Clean up build artifacts
    keep = {"problem.json", "solution.py", "io_pairs.json", "negative_pairs.json",
            "signature.txt", "task.dfy", "tests.dfy", "working_impl.dfy"}
    for f in problem_dir.iterdir():
        if f.name in keep:
            continue
        if f.is_dir():
            shutil.rmtree(f)
        else:
            f.unlink()

    elapsed = time.time() - start_time
    print(f"  SUCCESS in {elapsed:.0f}s")
    return True


def _process_worker(args_tuple):
    """Worker for parallel execution. Returns (idx, pid, success)."""
    problem, idx = args_tuple
    try:
        ok = process_problem(problem, idx)
    except Exception as e:
        pid = problem["id"].replace("/", "_")
        print(f"  [{idx}] EXCEPTION: {e}")
        ok = False
    pid = problem["id"].replace("/", "_")
    return idx, pid, ok


def main():
    import argparse
    from concurrent.futures import ProcessPoolExecutor, as_completed
    parser = argparse.ArgumentParser()
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--count", type=int, default=10)
    parser.add_argument("--max-rating", type=int, default=1600)
    parser.add_argument("--workers", type=int, default=1)
    args = parser.parse_args()

    DATASET_DIR.mkdir(exist_ok=True)
    QUEUE_DIR.mkdir(exist_ok=True)

    data = load_data()
    data = [p for p in data if p["rating"] <= args.max_rating]
    data.sort(key=lambda p: p["rating"])
    data = data[args.start:args.start + args.count]
    print(f"Processing {len(data)} problems with {args.workers} workers")

    success_count = 0
    fail_count = 0

    work_items = [(problem, args.start + i) for i, problem in enumerate(data)]

    if args.workers <= 1:
        # Sequential mode
        for problem, idx in work_items:
            _, pid, ok = _process_worker((problem, idx))
            problem_dir = DATASET_DIR / f"{idx:04d}_{pid}"
            if ok:
                success_count += 1
            else:
                fail_count += 1
                queue_dest = QUEUE_DIR / f"{idx:04d}_{pid}"
                if problem_dir.exists():
                    if queue_dest.exists():
                        shutil.rmtree(queue_dest)
                    shutil.move(str(problem_dir), str(queue_dest))
    else:
        # Parallel mode
        with ProcessPoolExecutor(max_workers=args.workers) as executor:
            futures = {executor.submit(_process_worker, item): item for item in work_items}
            for future in as_completed(futures):
                idx, pid, ok = future.result()
                problem_dir = DATASET_DIR / f"{idx:04d}_{pid}"
                if ok:
                    success_count += 1
                else:
                    fail_count += 1
                    queue_dest = QUEUE_DIR / f"{idx:04d}_{pid}"
                    if problem_dir.exists():
                        if queue_dest.exists():
                            shutil.rmtree(queue_dest)
                        shutil.move(str(problem_dir), str(queue_dest))
                print(f"  Progress: {success_count + fail_count}/{len(data)} done ({success_count} ok, {fail_count} failed)")

    print(f"\nDone: {success_count} success, {fail_count} failed (in queue/)")

    # Log all tests to a single file
    log_path = DATASET_DIR / "all_tests.txt"
    with open(log_path, "w") as f:
        f.write(f"Pipeline run at {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(f"{success_count} success, {fail_count} failed\n\n")
        for d in sorted(DATASET_DIR.iterdir()):
            if not d.is_dir():
                continue
            tests_file = d / "tests.dfy"
            if tests_file.exists():
                f.write(f"{'='*60}\n")
                f.write(f"{d.name}\n")
                f.write(f"{'='*60}\n")
                f.write(tests_file.read_text())
                f.write("\n\n")
    print(f"All tests logged to {log_path}")


if __name__ == "__main__":
    main()
