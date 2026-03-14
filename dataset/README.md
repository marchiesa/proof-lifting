# Dafny Verification Benchmark Dataset

## Purpose

This dataset contains algorithmic problems formulated as Dafny verification tasks.
Each problem provides a method with a formal specification (postcondition) and an
implementation, but **without loop invariants**. The task for an LLM is to add the
correct invariants so that Dafny can verify the program.

## Directory Structure

```
dataset/
  problems/
    {problem_id}/
      problem.md       -- Problem description in plain English
      task.dfy         -- Dafny file the LLM receives (spec + code, NO invariants)
      tests.dfy        -- Test cases validating the spec is correct
      reference.dfy    -- Ground truth verified solution WITH invariants
      metadata.json    -- Difficulty, category, source info
  scripts/
    generate_problem.py   -- Helper to scaffold a new problem
    validate_problem.sh   -- Validates all Dafny files compile/verify correctly
```

## Problem Format

### task.dfy

Contains:
- Predicate/function definitions that express the formal specification
- A method signature with `requires` and `ensures` clauses
- The implementation body with loops but **no `invariant` clauses**

The LLM's job is to add the missing invariants so Dafny verifies the program.

### tests.dfy

Contains test methods that:
- Call the implementation with known inputs
- Assert that the output satisfies the postcondition predicate
- Cover edge cases (empty inputs, single elements, boundary values)

### reference.dfy

The complete verified solution including all necessary:
- Loop invariants
- Decreases clauses
- Lemma calls (if needed)
- Ghost variables (if needed)

### metadata.json

```json
{
  "problem_id": "001_binary_search",
  "title": "Binary Search",
  "difficulty": "easy|medium|hard",
  "category": "searching",
  "tags": ["binary-search", "sorted-array"],
  "num_invariants": 3,
  "source": "classic algorithm",
  "description_brief": "One-line summary"
}
```

## Difficulty Levels

- **easy**: Simple loops with straightforward invariants (e.g., linear scan)
- **medium**: Multiple loops or non-obvious invariant relationships (e.g., binary search, two pointers)
- **hard**: Complex invariants involving mathematical properties, nested loops, or auxiliary lemmas (e.g., KMP, segment operations)

## Validation

Run the validation script to check all problems:

```bash
# Validate a single problem
./dataset/scripts/validate_problem.sh dataset/problems/001_binary_search

# Validate all problems
for d in dataset/problems/*/; do ./dataset/scripts/validate_problem.sh "$d"; done
```

The validator checks:
1. `task.dfy` compiles but does NOT verify (ensures the task is non-trivial)
2. `reference.dfy` both compiles and verifies (ensures the solution is correct)
3. `tests.dfy` compiles and verifies (ensures the spec is testable)

## Design Principles

1. **Unique outputs**: Each problem has a unique correct output for any given input,
   or the spec accepts any valid answer.
2. **Executable specs**: Postcondition predicates are executable (computable), not
   just type constraints.
3. **Non-trivial invariants**: Problems require more than just `0 <= i <= n` bounds.
4. **Idiomatic Dafny**: Uses sequences over arrays when possible; clean functional style.
5. **No I/O**: Methods take typed parameters and return typed results -- no stdin parsing.
