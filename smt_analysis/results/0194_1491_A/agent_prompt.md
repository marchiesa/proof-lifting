Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: K-th Largest Value
You are given an array $$$a$$$ consisting of $$$n$$$ integers. Initially all elements of $$$a$$$ are either $$$0$$$ or $$$1$$$. You need to process $$$q$$$ queries of two kinds:

- 1 x : Assign to $$$a_x$$$ the value $$$1 - a_x$$$.
- 2 k : Print the $$$k$$$-th largest value of the array.

As a reminder, $$$k$$$-th largest value of the array $$$b$$$ is defined as following:

- Sort the array in the non-increasing order, return $$$k$$$-th element from it.

For example, the second largest element in array $$$[0, 1, 0, 1]$$$ is $$$1$$$, as after sorting in non-increasing order it becomes $$$[1, 1, 0, 0]$$$, and the second element in this array is equal to $$$1$$$.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0194_1491_A/task.dfy

```dafny
// --- Specification: models the problem's operations and definitions ---

// Count of 1s in a sequence
ghost function Ones(a: seq<int>): int
  ensures 0 <= Ones(a) <= |a|
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[|a|-1] == 1 then 1 else 0) + Ones(a[..|a|-1])
}

// Build a sequence of n copies of value v
ghost function Repeat(v: int, n: int): seq<int>
  requires n >= 0
  ensures |Repeat(v, n)| == n
  decreases n
{
  if n == 0 then [] else Repeat(v, n - 1) + [v]
}

// All elements are 0 or 1
ghost predicate IsBinaryArray(a: seq<int>) {
  forall i | 0 <= i < |a| :: a[i] == 0 || a[i] == 1
}

// A sequence is in non-increasing order
ghost predicate IsNonIncreasing(a: seq<int>) {
  forall i, j | 0 <= i < j < |a| :: a[i] >= a[j]
}

// Queries are well-formed for an array of length n:
// type is 1 or 2, and the operand is in [1, n]
ghost predicate ValidQueries(n: int, queries: seq<(int, int)>) {
  forall i | 0 <= i < |queries| ::
    (queries[i].0 == 1 || queries[i].0 == 2) &&
    (queries[i].0 == 1 ==> 1 <= queries[i].1 <= n) &&
    (queries[i].0 == 2 ==> 1 <= queries[i].1 <= n)
}

// The array state after processing a sequence of queries:
// Type-1 queries flip the element at position x (1-indexed);
// Type-2 queries are observations that leave the array unchanged
ghost function ArrayState(init: seq<int>, queries: seq<(int, int)>): seq<int>
  requires ValidQueries(|init|, queries)
  ensures |ArrayState(init, queries)| == |init|
  decreases |queries|
{
  if |queries| == 0 then init
  else
    var prev := ArrayState(init, queries[..|queries|-1]);
    var q := queries[|queries|-1];
    if q.0 == 1 then prev[q.1 - 1 := 1 - prev[q.1 - 1]]
    else prev
}

// Sort a sequence in non-increasing order.
// For a binary array this places all 1s before all 0s —
// the direct definition of "sort descending" for {0,1} values.
ghost function SortDescending(a: seq<int>): seq<int>
  ensures |SortDescending(a)| == |a|
{
  Repeat(1, Ones(a)) + Repeat(0, |a| - Ones(a))
}

// The expected output: for each type-2 query, sort the current array
// state in non-increasing order and return the k-th element (1-indexed)
ghost function ExpectedResults(init: seq<int>, queries: seq<(int, int)>): seq<int>
  requires ValidQueries(|init|, queries)
  decreases |queries|
{
  if |queries| == 0 then []
  else
    var prev := ExpectedResults(init, queries[..|queries|-1]);
    var arr := ArrayState(init, queries[..|queries|-1]);
    var q := queries[|queries|-1];
    if q.0 == 2 then
      var sorted := SortDescending(arr);
      prev + [sorted[q.1 - 1]]
    else
      prev
}

// --- Method with specification ---

method KthLargestValue(a: seq<int>, queries: seq<(int, int)>) returns (results: seq<int>)
  requires IsBinaryArray(a)
  requires ValidQueries(|a|, queries)
  ensures results == ExpectedResults(a, queries)
{
  var arr := a;
  var s := 0;
  var i := 0;
  while i < |arr| {
    s := s + arr[i];
    i := i + 1;
  }

  results := [];
  i := 0;
  while i < |queries| {
    var t := queries[i].0;
    var x := queries[i].1;
    if t == 1 {
      s := s - arr[x - 1];
      arr := arr[x - 1 := 1 - arr[x - 1]];
      s := s + arr[x - 1];
    } else {
      if x <= s {
        results := results + [1];
      } else {
        results := results + [0];
      }
    }
    i := i + 1;
  }
}
```

## Instructions:

1. Read the code carefully. Understand what the method does and what the spec requires.

2. Add loop invariants for every loop. Common patterns:
   - Bounds: `invariant 0 <= i <= |s|`
   - Accumulator: `invariant acc == F(s[..i])` for recursive ghost functions
   - Sequence slicing: `assert s[..i+1] == s[..i] + [s[i]];` before using F(s[..i+1])
   - Full slice identity: `assert s[..|s|] == s;` after loops that process entire sequences
   - Type preservation: `invariant AllNonNeg(s[..i])` if needed by the spec

3. Add helper lemmas if needed (e.g., SumAppend, induction lemmas).

4. Run dafny verify:
   ```bash
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0194_1491_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0194_1491_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0194_1491_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0194_1491_A/ (create the directory if needed).
