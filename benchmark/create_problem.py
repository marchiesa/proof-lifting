#!/usr/bin/env python3
"""
Problem template generator for the Dafny verification benchmark.

Generates the skeleton directory and files for a new benchmark problem.

Usage:
    python create_problem.py --name "binary_search" --number 131 \
        --difficulty medium --algorithm "binary search"
"""

import argparse
import json
import os
import sys
from pathlib import Path


def to_title(name: str) -> str:
    """Convert snake_case name to Title Case."""
    return name.replace("_", " ").title()


def to_method_name(name: str) -> str:
    """Convert snake_case name to PascalCase method name."""
    return "".join(word.capitalize() for word in name.split("_"))


def create_task_dfy(title: str, method_name: str) -> str:
    """Generate task.dfy template."""
    return f"""// {title}
// Task: Add loop invariants so that Dafny can verify this program.
// Do NOT modify the code logic, method signature, or specification.

// TODO: Define spec predicates here (non-ghost, so they can be tested at runtime)
// predicate Spec{method_name}(/* params */)
// {{
//   // specification
// }}

// TODO: Implement method with correct algorithm
method {method_name}(/* params */) returns (/* returns */)
  // requires ...
  // ensures ...
{{
  // TODO: algorithm here
}}
"""


def create_reference_dfy(title: str, method_name: str) -> str:
    """Generate reference.dfy template."""
    return f"""// {title} -- Reference solution
// This file should verify completely with `dafny verify reference.dfy`.

// TODO: Copy spec predicates from task.dfy

// TODO: Copy method from task.dfy and add loop invariants, assertions, lemmas
method {method_name}(/* params */) returns (/* returns */)
  // requires ...
  // ensures ...
{{
  // TODO: algorithm with invariants here
}}
"""


def create_tests_dfy(title: str, method_name: str) -> str:
    """Generate tests.dfy template."""
    return f"""// {title} -- Tests
// These tests validate both the specification predicates and the implementation.
// Use `dafny run tests.dfy` to execute.

// =============================================
// Section 1: Spec predicate tests
// =============================================
// TODO: Copy spec predicates from task.dfy here (non-ghost, bounded quantifiers).
// If the spec uses quantifiers, use bounded quantifiers for compilability.
// For example, replace `forall i :: 0 <= i < |s| ==> ...`
// with an equivalent compilable form.

// predicate Spec{method_name}(/* params */)
// {{
//   // specification predicate
// }}

// =============================================
// Section 2: Implementation tests
// =============================================
// Include the full implementation from reference.dfy so the method can be called.
// If `include` does not work, copy the method into this file instead.

include "reference.dfy"

method Main() {{
  // --- Test the spec ---
  // TODO: Test spec with positive cases
  // expect Spec{method_name}(input, expected_output), "spec should accept correct answer";

  // TODO: Test spec with negative cases
  // expect !Spec{method_name}(input, wrong_output), "spec should reject wrong answer";

  // TODO: Test edge cases
  // expect Spec{method_name}(empty_input, expected), "edge case description";

  // --- Test the implementation ---
  // TODO: Call the method with concrete inputs and check outputs
  // var result := {method_name}(input);
  // expect result == expected, "implementation should return correct answer";
  // Or if exact equality isn't possible:
  // expect Spec{method_name}(input, result), "implementation output should satisfy spec";

  print "All tests passed\\n";
}}
"""


def create_problem_md(title: str, method_name: str, difficulty: str, algorithm: str) -> str:
    """Generate problem.md template."""
    return f"""# {title}

## Difficulty

{difficulty}

## Algorithm

{algorithm}

## Description

TODO: Describe the problem and what the method should accomplish.

## Specification

TODO: Describe the formal specification (preconditions, postconditions).

## Hints

TODO: Describe what invariants or proof annotations are needed.
"""


def create_metadata_json(
    name: str, number: int, difficulty: str, algorithm: str
) -> str:
    """Generate metadata.json."""
    data = {
        "number": number,
        "name": name,
        "difficulty": difficulty,
        "algorithm": algorithm,
        "tags": [],
        "source": "",
    }
    return json.dumps(data, indent=2) + "\n"


def main():
    parser = argparse.ArgumentParser(
        description="Generate a new benchmark problem skeleton"
    )
    parser.add_argument(
        "--name",
        required=True,
        help="Problem name in snake_case (e.g., binary_search)",
    )
    parser.add_argument(
        "--number",
        type=int,
        required=True,
        help="Problem number (e.g., 131)",
    )
    parser.add_argument(
        "--difficulty",
        required=True,
        choices=["easy", "medium", "hard"],
        help="Problem difficulty",
    )
    parser.add_argument(
        "--algorithm",
        required=True,
        help='Algorithm category (e.g., "binary search", "dynamic programming")',
    )
    parser.add_argument(
        "--dataset-dir",
        default=None,
        help="Path to dataset/problems directory (default: ./dataset/problems relative to this script)",
    )

    args = parser.parse_args()

    # Determine output directory
    if args.dataset_dir:
        base_dir = args.dataset_dir
    else:
        base_dir = os.path.join(
            os.path.dirname(os.path.abspath(__file__)),
            "dataset",
            "problems",
        )

    dir_name = f"{args.number}_{args.name}"
    problem_dir = os.path.join(base_dir, dir_name)

    if os.path.exists(problem_dir):
        print(f"ERROR: Directory already exists: {problem_dir}", file=sys.stderr)
        sys.exit(1)

    title = to_title(args.name)
    method_name = to_method_name(args.name)

    # Create directory and files
    os.makedirs(problem_dir, exist_ok=True)

    files = {
        "task.dfy": create_task_dfy(title, method_name),
        "reference.dfy": create_reference_dfy(title, method_name),
        "tests.dfy": create_tests_dfy(title, method_name),
        "problem.md": create_problem_md(title, method_name, args.difficulty, args.algorithm),
        "metadata.json": create_metadata_json(args.name, args.number, args.difficulty, args.algorithm),
    }

    for filename, content in files.items():
        filepath = os.path.join(problem_dir, filename)
        with open(filepath, "w") as f:
            f.write(content)
        print(f"  Created {filepath}")

    print(f"\nProblem skeleton created at: {problem_dir}")
    print(f"\nNext steps:")
    print(f"  1. Edit task.dfy with the actual specification and algorithm")
    print(f"  2. Edit reference.dfy with the verified solution (add invariants)")
    print(f"  3. Edit tests.dfy with spec predicate tests AND implementation tests")
    print(f"  4. Edit problem.md with the problem description")
    print(f"  5. Run: python validate_dataset.py --dataset {base_dir} --problems {dir_name}")


if __name__ == "__main__":
    main()
