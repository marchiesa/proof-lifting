#!/usr/bin/env python3
"""
Prepare benchmark inputs: strip essential assertions from verified code.

For each verified problem with essential assertions, produces:
  - stripped.dfy: verified code with ALL essential assertions removed
  - prompt.txt: the prompt to send to the LLM
  - meta.json: problem metadata (original assertions, which were removed, etc.)

Usage:
    python3 smt_analysis/benchmark/prepare.py
    python3 smt_analysis/benchmark/prepare.py --names 0000_1013_A 0003_1028_A
    python3 smt_analysis/benchmark/prepare.py --tar  # also create benchmark_inputs.tar.gz
"""

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

PROJ_ROOT = Path(__file__).parent.parent.parent.resolve()
RESULTS_DIR = PROJ_ROOT / "smt_analysis" / "results"
BENCHMARK_DIR = PROJ_ROOT / "smt_analysis" / "benchmark" / "inputs"

sys.path.insert(0, str(PROJ_ROOT / "smt_analysis"))
from fast_diagnose import _find_assert_end


def strip_essential_assertions(source_path: Path, assertions: list[dict]) -> str:
    """Remove all essential assertions from the source file.

    Returns the stripped source code.
    """
    lines = source_path.read_text().split("\n")

    # Sort by line number descending so removals don't shift later line numbers
    essentials = sorted(assertions, key=lambda a: a["line"], reverse=True)

    for a in essentials:
        start = a["line"] - 1
        if start < 0 or start >= len(lines):
            continue

        stripped = lines[start].strip()

        if stripped.startswith("assert "):
            # Standalone assert — find full extent (including by-block)
            end = _find_assert_end(lines, start)
            for j in range(start, end + 1):
                lines[j] = ""
        else:
            # Inline assert — surgically remove
            expr_text = a.get("text", "")
            # Try removing "assert <expr>;" from the line
            for pattern in [expr_text, f" {expr_text}"]:
                if pattern in lines[start]:
                    lines[start] = lines[start].replace(pattern, "", 1)
                    break

    # Clean up blank lines (collapse multiple blank lines)
    result = []
    prev_blank = False
    for line in lines:
        is_blank = line.strip() == ""
        if is_blank and prev_blank:
            continue
        result.append(line)
        prev_blank = is_blank

    return "\n".join(result)


def build_prompt(stripped_code: str, problem_name: str) -> str:
    """Build the prompt for the LLM."""
    return f"""The following Dafny program has a correct implementation and specification, but verification fails because some `assert` statements are missing. The program verified successfully before these assertions were removed.

RULES — read carefully:
1. Add `assert` statements to make `dafny verify` pass.
2. You may add helper lemmas or ghost functions if needed.
3. You MUST NOT modify ANY existing code. Do not change variable names, assignments, control flow, loop bodies, if/else branches, return statements, or any expression.
4. You MUST NOT modify ANY formal specification. Do not change requires, ensures, invariant, decreases, function bodies, or predicate bodies.
5. Any modification to existing code or specifications will be automatically detected and rejected. We compare the AST of your output against the original — only added assert statements and new lemma/function definitions are permitted.

Return ONLY the complete Dafny program with your added assertions. No explanations.

```dafny
{stripped_code}
```"""


def prepare_problem(problem_name: str) -> dict | None:
    """Prepare benchmark input for one problem."""
    problem_dir = RESULTS_DIR / problem_name
    ablation_path = problem_dir / "ablation" / "results.json"

    if not ablation_path.exists():
        return None

    ablation = json.loads(ablation_path.read_text())
    essential = [a for a in ablation["results"] if a.get("essential")]

    if not essential:
        return None

    # Pick source file
    source_file = problem_dir / "verified_inlined.dfy"
    if source_file.exists():
        content = source_file.read_text()
        if not re.search(r'\bmethod\s+\w+', content):
            source_file = problem_dir / "verified.dfy"
    else:
        source_file = problem_dir / "verified.dfy"

    if not source_file.exists():
        return None

    # Strip essential assertions
    stripped = strip_essential_assertions(source_file, essential)

    # Build prompt
    prompt = build_prompt(stripped, problem_name)

    # Write outputs
    out_dir = BENCHMARK_DIR / problem_name
    out_dir.mkdir(parents=True, exist_ok=True)

    (out_dir / "stripped.dfy").write_text(stripped)
    (out_dir / "prompt.txt").write_text(prompt)

    # Generate fresh reference AST mapping (needs modified Dafny with body serialization)
    dotnet = os.environ.get("DOTNET8", os.environ.get("DOTNET", "dotnet"))
    dafny_dll = os.environ.get("DAFNY_DLL",
        str(PROJ_ROOT / "dafny-source" / "Binaries" / "Dafny.dll"))
    ref_ast_path = out_dir / "reference_ast.json"
    subprocess.run(
        [dotnet, dafny_dll, "verify", str(source_file),
         "--ast-mapping", str(ref_ast_path),
         "--verification-time-limit", "60"],
        capture_output=True, text=True, timeout=120,
    )

    meta = {
        "problem": problem_name,
        "source_file": source_file.name,
        "total_assertions": ablation["total"],
        "essential_count": len(essential),
        "essential_assertions": [
            {"line": a["line"], "text": a["text"]}
            for a in essential
        ],
        "original_code": source_file.read_text(),
    }
    (out_dir / "meta.json").write_text(json.dumps(meta, indent=2))

    return meta


def main():
    parser = argparse.ArgumentParser(description="Prepare benchmark inputs")
    parser.add_argument("--names", nargs="+", help="Specific problem names")
    parser.add_argument("--tar", action="store_true", help="Create tar.gz archive")
    args = parser.parse_args()

    verified_path = RESULTS_DIR / "verified_problems.txt"
    verified = set(verified_path.read_text().split()) if verified_path.exists() else set()

    if args.names:
        names = args.names
    else:
        # All verified problems with essential assertions
        names = []
        for d in sorted(RESULTS_DIR.iterdir()):
            if not d.is_dir() or d.name not in verified:
                continue
            r = d / "ablation" / "results.json"
            if r.exists():
                data = json.loads(r.read_text())
                if data["essential_count"] > 0:
                    names.append(d.name)

    print(f"Preparing {len(names)} problems...")

    prepared = []
    for name in names:
        meta = prepare_problem(name)
        if meta:
            prepared.append(meta)
            print(f"  {name}: {meta['essential_count']} essential assertions stripped")

    # Write manifest
    BENCHMARK_DIR.mkdir(parents=True, exist_ok=True)
    manifest = {
        "total_problems": len(prepared),
        "problems": [p["problem"] for p in prepared],
        "total_essential": sum(p["essential_count"] for p in prepared),
    }
    (BENCHMARK_DIR / "manifest.json").write_text(json.dumps(manifest, indent=2))
    print(f"\nPrepared {len(prepared)} problems, {manifest['total_essential']} essential assertions")

    if args.tar:
        import tarfile
        tar_path = PROJ_ROOT / "smt_analysis" / "benchmark" / "benchmark_inputs.tar.gz"
        with tarfile.open(tar_path, "w:gz") as tar:
            tar.add(BENCHMARK_DIR, arcname="inputs")
        print(f"Archive: {tar_path}")


if __name__ == "__main__":
    main()
