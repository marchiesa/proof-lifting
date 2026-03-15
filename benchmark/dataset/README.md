# Benchmark Dataset

This directory contains the problem set for the Dafny verification benchmark.

## Problem Structure

Each problem lives in a subdirectory under `problems/` named `<number>_<name>` (e.g., `131_binary_search`). Every problem directory must contain:

| File | Description |
|------|-------------|
| `task.dfy` | The Dafny program with specification but missing proof annotations. This is what the LLM receives. |
| `reference.dfy` | A fully verified reference solution (with invariants, assertions, lemmas). Must verify with 0 errors. |
| `tests.dfy` | Runtime tests that validate both spec predicates and the implementation. Must compile and run with `dafny run`. |
| `problem.md` | Human-readable description of the problem, hints, and expected difficulty. |
| `metadata.json` | Machine-readable metadata with at least `difficulty` and `algorithm` fields. |

## Runtime Tests

Every problem **must** include `tests.dfy` with runtime tests for both the specification predicates and the implementation. This ensures that the spec describes the intended behavior and the implementation actually produces correct results.

### Requirements for `tests.dfy`

1. Must contain a `Main` method
2. Must use `expect` statements (not `assert`) for runtime-checkable tests
3. Must include both positive and negative spec test cases
4. Must include implementation tests that call the method and check outputs
5. Spec predicates should be copied from `task.dfy` and made compilable (use bounded quantifiers)
6. The implementation should be included from `reference.dfy` (or copied if `include` doesn't work)

### Example

```dafny
// Tests for IsSorted / SortArray

// =============================================
// Section 1: Spec predicate tests
// =============================================

predicate IsSorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// =============================================
// Section 2: Implementation tests
// =============================================

include "reference.dfy"

method Main() {
  // --- Test the spec ---
  // Positive cases
  expect IsSorted([]), "empty sequence is sorted";
  expect IsSorted([1]), "singleton is sorted";
  expect IsSorted([1, 2, 3]), "ascending sequence is sorted";

  // Negative cases
  expect !IsSorted([3, 1]), "descending pair is not sorted";
  expect !IsSorted([1, 3, 2]), "out-of-order element means not sorted";

  // --- Test the implementation ---
  var result := SortArray([3, 1, 2]);
  expect result == [1, 2, 3], "implementation should sort correctly";
  expect IsSorted(result), "implementation output should satisfy spec";

  var empty := SortArray([]);
  expect empty == [], "implementation should handle empty input";

  print "All tests passed\n";
}
```

### Ghost vs Non-Ghost Predicates

Spec predicates in `task.dfy` should be **non-ghost** so they can be tested at runtime. If a predicate must be ghost for Dafny reasons, the `tests.dfy` file should redefine a compilable version for testing.

## Validating the Dataset

Use the validation script to check all problems:

```bash
# Validate all problems (with dafny checks)
python benchmark/validate_dataset.py \
    --dataset benchmark/dataset/problems \
    --dafny "/opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /path/to/Dafny.dll"

# Validate without running dafny (file structure checks only)
python benchmark/validate_dataset.py \
    --dataset benchmark/dataset/problems \
    --skip-dafny

# Validate specific problems
python benchmark/validate_dataset.py \
    --dataset benchmark/dataset/problems \
    --dafny "..." \
    --problems sum_array reverse_array
```

The validator checks:
- All required files exist
- `task.dfy` parses without errors
- `reference.dfy` verifies completely (0 errors)
- `tests.dfy` compiles and runs successfully
- `tests.dfy` has a `Main` method and `expect` statements
- `tests.dfy` includes implementation tests (method calls with output checks)
- `metadata.json` has required fields
- Spec predicates are non-ghost (warning if ghost)

## Creating New Problems

Use the problem template generator:

```bash
python benchmark/create_problem.py \
    --name "binary_search" \
    --number 131 \
    --difficulty medium \
    --algorithm "binary search"
```

This creates `dataset/problems/131_binary_search/` with skeleton files for all required components.

After generating, fill in the templates:
1. Write the spec predicates and method in `task.dfy`
2. Add proof annotations to `reference.dfy` so it verifies
3. Write spec predicate tests AND implementation tests in `tests.dfy`
4. Describe the problem in `problem.md`
5. Validate with `python benchmark/validate_dataset.py`

## Running the Benchmark

The benchmark runner automatically runs tests (spec + implementation) after successful verification:

```bash
# Normal run (includes tests)
python benchmark/run_benchmark.py --dataset benchmark/dataset/problems --adapter claude_code

# Skip tests
python benchmark/run_benchmark.py --dataset benchmark/dataset/problems --adapter claude_code --skip-tests
```

Problems that verify but fail tests are marked as `TEST_FAIL` in the results.
