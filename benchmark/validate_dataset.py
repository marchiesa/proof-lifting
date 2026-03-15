#!/usr/bin/env python3
"""
Dataset validation script for the Dafny verification benchmark.

Checks every problem in a dataset directory for required files, correct
structure, and basic compilability/runnability.

Usage:
    python validate_dataset.py --dataset ./dataset/problems \
        --dafny "/opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /path/to/Dafny.dll"
"""

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple


# ── Check definitions ────────────────────────────────────────────────

REQUIRED_FILES = ["task.dfy", "reference.dfy", "tests.dfy", "problem.md", "metadata.json"]
REQUIRED_METADATA_FIELDS = ["difficulty", "algorithm"]


def check_required_files(problem_dir: str) -> Tuple[bool, str]:
    """Check that all required files exist."""
    missing = []
    for fname in REQUIRED_FILES:
        if not os.path.exists(os.path.join(problem_dir, fname)):
            missing.append(fname)
    if missing:
        return False, f"Missing: {', '.join(missing)}"
    return True, "All required files present"


def check_task_parses(problem_dir: str, dafny_cmd: str) -> Tuple[bool, str]:
    """Check that task.dfy parses without parse/resolve errors."""
    task_file = os.path.join(problem_dir, "task.dfy")
    if not os.path.exists(task_file):
        return False, "task.dfy not found"

    cmd_parts = dafny_cmd.split()
    # Use 'dafny verify' but only check for parse/resolve errors
    cmd = cmd_parts + ["verify", task_file]
    try:
        result = subprocess.run(
            cmd, capture_output=True, text=True, timeout=120
        )
        output = result.stdout + result.stderr
        # Parse errors and resolution errors indicate structural issues
        # Verification errors are expected (that's the point of the task)
        parse_errors = re.findall(r"Error:.*[Pp]arse|[Pp]arse.*[Ee]rror", output)
        resolve_errors = re.findall(r"Error:.*not found|Error:.*does not exist|Error:.*[Uu]nresolved", output)
        type_errors = re.findall(r"Error:.*type", output, re.IGNORECASE)

        # Filter to only parse/type errors (not verification failures)
        has_parse_issues = bool(parse_errors or resolve_errors)

        if has_parse_issues:
            return False, f"Parse/resolve errors found"
        return True, "Parses successfully"
    except subprocess.TimeoutExpired:
        return False, "Timed out"
    except Exception as e:
        return False, f"Error: {e}"


def check_reference_verifies(problem_dir: str, dafny_cmd: str) -> Tuple[bool, str]:
    """Check that reference.dfy verifies completely (0 errors)."""
    ref_file = os.path.join(problem_dir, "reference.dfy")
    if not os.path.exists(ref_file):
        return False, "reference.dfy not found"

    cmd_parts = dafny_cmd.split()
    cmd = cmd_parts + ["verify", ref_file]
    try:
        result = subprocess.run(
            cmd, capture_output=True, text=True, timeout=120
        )
        output = result.stdout + result.stderr
        if result.returncode == 0:
            return True, "Verifies successfully"
        # Count errors
        error_match = re.search(r"(\d+)\s+error", output)
        error_count = error_match.group(1) if error_match else "unknown"
        return False, f"Verification failed ({error_count} errors)"
    except subprocess.TimeoutExpired:
        return False, "Timed out"
    except Exception as e:
        return False, f"Error: {e}"


def check_tests_run(problem_dir: str, dafny_cmd: str) -> Tuple[bool, str]:
    """Check that tests.dfy compiles and runs successfully."""
    tests_file = os.path.join(problem_dir, "tests.dfy")
    if not os.path.exists(tests_file):
        return False, "tests.dfy not found"

    cmd_parts = dafny_cmd.split()
    cmd = cmd_parts + ["run", tests_file]
    try:
        result = subprocess.run(
            cmd, capture_output=True, text=True, timeout=120
        )
        output = result.stdout + result.stderr
        if result.returncode == 0:
            return True, "Runs successfully"
        return False, f"Run failed: {output[:200]}"
    except subprocess.TimeoutExpired:
        return False, "Timed out"
    except Exception as e:
        return False, f"Error: {e}"


def check_tests_has_main(problem_dir: str) -> Tuple[bool, str]:
    """Check that tests.dfy contains a Main method."""
    tests_file = os.path.join(problem_dir, "tests.dfy")
    if not os.path.exists(tests_file):
        return False, "tests.dfy not found"

    content = Path(tests_file).read_text()
    if re.search(r"\bmethod\s+Main\s*\(", content):
        return True, "Main method found"
    return False, "No Main method found"


def check_tests_has_expects(problem_dir: str) -> Tuple[bool, str]:
    """Check that tests.dfy contains expect statements (not just asserts)."""
    tests_file = os.path.join(problem_dir, "tests.dfy")
    if not os.path.exists(tests_file):
        return False, "tests.dfy not found"

    content = Path(tests_file).read_text()
    expect_count = len(re.findall(r"\bexpect\b", content))
    if expect_count > 0:
        return True, f"{expect_count} expect statement(s) found"
    return False, "No expect statements found (use expect instead of assert for runtime tests)"


def check_tests_has_impl_tests(problem_dir: str) -> Tuple[bool, str]:
    """Check that tests.dfy includes implementation tests (calls the method and checks output)."""
    tests_file = os.path.join(problem_dir, "tests.dfy")
    if not os.path.exists(tests_file):
        return False, "tests.dfy not found"

    content = Path(tests_file).read_text()

    # Look for signs of implementation testing:
    # 1. include "reference.dfy" or the method being defined/copied
    # 2. var result := MethodName(...) pattern (method call with assignment)
    # 3. Comments indicating implementation test section

    has_include_ref = bool(re.search(r'include\s+["\'].*reference\.dfy["\']', content))

    # Look for method calls with var assignment: var x := MethodName(...)
    has_method_call = bool(re.search(r'\bvar\b\s+\w+\s*:=\s*\w+\s*\(', content))

    # Look for Section 2 marker comment
    has_impl_section = bool(re.search(r'(?i)implementation\s+tests?', content))

    if has_method_call:
        details = []
        if has_include_ref:
            details.append("includes reference.dfy")
        if has_impl_section:
            details.append("has impl test section")
        return True, f"Implementation tests found ({', '.join(details) if details else 'method calls detected'})"

    return False, "No implementation tests found (should call the method and check output with expect)"


def check_metadata_fields(problem_dir: str) -> Tuple[bool, str]:
    """Check that metadata.json has required fields."""
    meta_file = os.path.join(problem_dir, "metadata.json")
    if not os.path.exists(meta_file):
        return False, "metadata.json not found"

    try:
        with open(meta_file, "r") as f:
            data = json.load(f)
    except json.JSONDecodeError as e:
        return False, f"Invalid JSON: {e}"

    missing = [field for field in REQUIRED_METADATA_FIELDS if field not in data]
    if missing:
        return False, f"Missing fields: {', '.join(missing)}"
    return True, f"Required fields present (difficulty={data.get('difficulty')})"


def check_spec_non_ghost(problem_dir: str) -> Tuple[bool, str]:
    """Check if spec predicates in task.dfy are non-ghost (warn if ghost)."""
    task_file = os.path.join(problem_dir, "task.dfy")
    if not os.path.exists(task_file):
        return False, "task.dfy not found"

    content = Path(task_file).read_text()
    # Look for ghost predicates/functions
    ghost_matches = re.findall(r'\bghost\s+(predicate|function)\s+(\w+)', content)
    if ghost_matches:
        names = [f"{kind} {name}" for kind, name in ghost_matches]
        return False, f"WARN: Ghost spec items: {', '.join(names)} (should be non-ghost for testing)"
    return True, "No ghost spec predicates"


# ── Check registry ───────────────────────────────────────────────────

# Each check is (name, function, needs_dafny)
CHECKS = [
    ("required_files", check_required_files, False),
    ("task_parses", check_task_parses, True),
    ("reference_verifies", check_reference_verifies, True),
    ("tests_run", check_tests_run, True),
    ("tests_has_main", check_tests_has_main, False),
    ("tests_has_expects", check_tests_has_expects, False),
    ("tests_has_impl_tests", check_tests_has_impl_tests, False),
    ("metadata_fields", check_metadata_fields, False),
    ("spec_non_ghost", check_spec_non_ghost, False),
]


# ── Main logic ────────────────────────────────────────────────────────


def validate_problem(
    problem_dir: str, dafny_cmd: Optional[str], skip_dafny: bool = False
) -> Dict[str, Tuple[bool, str]]:
    """Run all checks on a single problem directory. Returns dict of check_name -> (passed, message)."""
    results = {}
    for name, func, needs_dafny in CHECKS:
        if needs_dafny and (skip_dafny or not dafny_cmd):
            results[name] = (None, "Skipped (no dafny)")
            continue
        if needs_dafny:
            results[name] = func(problem_dir, dafny_cmd)
        else:
            results[name] = func(problem_dir)
    return results


def discover_problems(dataset_dir: str) -> List[str]:
    """Find all problem subdirectories (those containing task.dfy or any .dfy file)."""
    problems = []
    dataset_path = Path(dataset_dir)
    if not dataset_path.exists():
        print(f"ERROR: Dataset directory does not exist: {dataset_dir}", file=sys.stderr)
        sys.exit(1)

    for entry in sorted(dataset_path.iterdir()):
        if entry.is_dir():
            problems.append(str(entry))
    return problems


def print_summary_table(
    all_results: Dict[str, Dict[str, Tuple[bool, str]]]
) -> int:
    """Print a summary table and return the number of problems with failures."""
    check_names = [name for name, _, _ in CHECKS]

    # Determine column widths
    problem_width = max(len("Problem"), max(len(os.path.basename(p)) for p in all_results))
    col_width = 10

    # Header
    header = f"{'Problem':<{problem_width}}"
    for cn in check_names:
        # Abbreviate check names
        short = cn[:col_width]
        header += f"  {short:>{col_width}}"
    print(header)
    print("-" * len(header))

    failure_count = 0

    for problem_path, checks in all_results.items():
        problem_name = os.path.basename(problem_path)
        row = f"{problem_name:<{problem_width}}"
        has_failure = False
        for cn in check_names:
            passed, msg = checks.get(cn, (None, "N/A"))
            if passed is True:
                symbol = "PASS"
            elif passed is False:
                if "WARN" in msg:
                    symbol = "WARN"
                else:
                    symbol = "FAIL"
                    has_failure = True
            else:
                symbol = "SKIP"
            row += f"  {symbol:>{col_width}}"
        print(row)

        if has_failure:
            failure_count += 1

    print("-" * len(header))
    total = len(all_results)
    passed = total - failure_count
    print(f"\nSummary: {passed}/{total} problems pass all checks")

    # Print details for failures
    has_details = False
    for problem_path, checks in all_results.items():
        problem_name = os.path.basename(problem_path)
        failures = [
            (cn, msg)
            for cn in check_names
            for passed, msg in [checks.get(cn, (None, ""))]
            if passed is False
        ]
        if failures:
            if not has_details:
                print("\nDetails:")
                has_details = True
            print(f"\n  {problem_name}:")
            for cn, msg in failures:
                print(f"    {cn}: {msg}")

    return failure_count


def main():
    parser = argparse.ArgumentParser(
        description="Validate a Dafny benchmark dataset"
    )
    parser.add_argument(
        "--dataset",
        required=True,
        help="Path to dataset directory containing problem subdirectories",
    )
    parser.add_argument(
        "--dafny",
        default=None,
        help="Command to run dafny (e.g., 'dotnet /path/to/Dafny.dll'). "
             "If not provided, dafny-dependent checks are skipped.",
    )
    parser.add_argument(
        "--skip-dafny",
        action="store_true",
        default=False,
        help="Skip all checks that require running dafny",
    )
    parser.add_argument(
        "--problems",
        nargs="*",
        default=None,
        help="Specific problem names to validate (default: all)",
    )

    args = parser.parse_args()

    # Discover problems
    problem_dirs = discover_problems(args.dataset)
    if not problem_dirs:
        print("ERROR: No problem directories found", file=sys.stderr)
        sys.exit(1)

    # Filter to specific problems if requested
    if args.problems:
        problem_dirs = [
            p for p in problem_dirs
            if os.path.basename(p) in args.problems
        ]
        if not problem_dirs:
            print(f"ERROR: None of the specified problems found: {args.problems}", file=sys.stderr)
            sys.exit(1)

    print(f"Validating {len(problem_dirs)} problems in {args.dataset}")
    if args.dafny:
        print(f"Dafny command: {args.dafny}")
    else:
        print("No dafny command provided; dafny-dependent checks will be skipped")
    print()

    # Run validation
    all_results = {}
    for problem_dir in problem_dirs:
        problem_name = os.path.basename(problem_dir)
        print(f"  Checking {problem_name}...", end="", flush=True)
        results = validate_problem(problem_dir, args.dafny, args.skip_dafny)
        all_results[problem_dir] = results
        failures = sum(1 for passed, _ in results.values() if passed is False)
        if failures:
            print(f" {failures} issue(s)")
        else:
            print(" OK")

    print()
    failure_count = print_summary_table(all_results)

    sys.exit(1 if failure_count > 0 else 0)


if __name__ == "__main__":
    main()
