#!/usr/bin/env python3
"""
Scaffold a new problem directory for the Dafny verification benchmark dataset.

Usage:
    python generate_problem.py <problem_id> <title> <difficulty> <category> [--tags tag1,tag2]

Example:
    python generate_problem.py 001_binary_search "Binary Search" medium searching --tags binary-search,sorted-array
"""

import argparse
import json
import os
import sys


def create_problem(problem_id: str, title: str, difficulty: str, category: str, tags: list[str]):
    script_dir = os.path.dirname(os.path.abspath(__file__))
    problems_dir = os.path.join(script_dir, "..", "problems", problem_id)

    if os.path.exists(problems_dir):
        print(f"Error: Problem directory already exists: {problems_dir}")
        sys.exit(1)

    os.makedirs(problems_dir, exist_ok=True)

    # metadata.json
    metadata = {
        "problem_id": problem_id,
        "title": title,
        "difficulty": difficulty,
        "category": category,
        "tags": tags,
        "num_invariants": 0,
        "source": "",
        "description_brief": ""
    }
    with open(os.path.join(problems_dir, "metadata.json"), "w") as f:
        json.dump(metadata, f, indent=2)
        f.write("\n")

    # problem.md
    with open(os.path.join(problems_dir, "problem.md"), "w") as f:
        f.write(f"# {title}\n\n")
        f.write("## Description\n\n")
        f.write("TODO: Describe the problem.\n\n")
        f.write("## Input\n\n")
        f.write("TODO: Describe inputs.\n\n")
        f.write("## Output\n\n")
        f.write("TODO: Describe the expected output.\n\n")
        f.write("## Examples\n\n")
        f.write("TODO: Provide examples.\n")

    # task.dfy
    with open(os.path.join(problems_dir, "task.dfy"), "w") as f:
        f.write(f"// {title}\n")
        f.write("// Task: Add loop invariants so that Dafny can verify this program.\n\n")
        f.write("// TODO: Add spec predicates/functions\n\n")
        f.write("// TODO: Add method with requires/ensures but NO invariants\n")

    # reference.dfy
    with open(os.path.join(problems_dir, "reference.dfy"), "w") as f:
        f.write(f"// {title} -- Reference solution with invariants\n\n")
        f.write("// TODO: Add complete verified solution\n")

    # tests.dfy
    with open(os.path.join(problems_dir, "tests.dfy"), "w") as f:
        f.write(f"// {title} -- Test cases\n\n")
        f.write("// TODO: Add test methods\n")

    print(f"Created problem scaffold at: {problems_dir}")
    print(f"Files: problem.md, task.dfy, reference.dfy, tests.dfy, metadata.json")


def main():
    parser = argparse.ArgumentParser(description="Scaffold a new Dafny benchmark problem")
    parser.add_argument("problem_id", help="Problem ID (e.g., 001_binary_search)")
    parser.add_argument("title", help="Problem title")
    parser.add_argument("difficulty", choices=["easy", "medium", "hard"], help="Difficulty level")
    parser.add_argument("category", help="Category (e.g., searching, sorting, dp)")
    parser.add_argument("--tags", default="", help="Comma-separated tags")

    args = parser.parse_args()
    tags = [t.strip() for t in args.tags.split(",") if t.strip()] if args.tags else []
    create_problem(args.problem_id, args.title, args.difficulty, args.category, tags)


if __name__ == "__main__":
    main()
