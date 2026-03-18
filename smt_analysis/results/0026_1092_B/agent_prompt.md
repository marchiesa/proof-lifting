Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Teams Forming
There are $$$n$$$ students in a university. The number of students is even. The $$$i$$$-th student has programming skill equal to $$$a_i$$$.

The coach wants to form $$$\frac{n}{2}$$$ teams. Each team should consist of exactly two students, and each student should belong to exactly one team. Two students can form a team only if their skills are equal (otherwise they cannot understand each other and cannot form a team).

Students can solve problems to increase their skill. One solved problem increases the skill by one.

The coach wants to know the minimum total number of problems students should solve to form exactly $$$\frac{n}{2}$$$ teams (i.e. each pair of students should form a team). Your task is to find this number.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0026_1092_B/task.dfy

```dafny
// ===== Specification for Teams Forming =====
// Problem: Pair n students into n/2 teams. Students may increase their
// skill (cost 1 each). Paired students must end with equal skills.
// Minimize total cost.
//
// A valid team assignment (d, p) has non-negative increases d[i] and a
// permutation p pairing students so that each team has equal final skills.
// The answer minimizes SumSeq(d) over all valid (d, p).
//
// The minimum equals the sum of consecutive-pair differences after sorting,
// by the rearrangement inequality.

ghost function Abs(x: int): int {
  if x >= 0 then x else -x
}

ghost function SumSeq(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else SumSeq(s[..|s| - 1]) + s[|s| - 1]
}

// A permutation of {0, 1, ..., n-1}
ghost predicate IsPermutation(p: seq<int>, n: int) {
  |p| == n &&
  (forall i | 0 <= i < n :: 0 <= p[i] < n) &&
  (forall i, j | 0 <= i < j < n :: p[i] != p[j])
}

// A valid team assignment: non-negative increases d, permutation p,
// with equal final skills within each team k = (p[2k], p[2k+1])
ghost predicate ValidTeamAssignment(a: seq<int>, d: seq<int>, p: seq<int>)
  requires |a| % 2 == 0
{
  var n := |a|;
  |d| == n && IsPermutation(p, n) &&
  (forall i | 0 <= i < n :: d[i] >= 0) &&
  (forall k | 0 <= k < n / 2 ::
    a[p[2 * k]] + d[p[2 * k]] == a[p[2 * k + 1]] + d[p[2 * k + 1]])
}

// The cost of a team assignment is the total number of skill increases
ghost function AssignmentCost(d: seq<int>): int {
  SumSeq(d)
}

// Functional insertion sort
ghost function InsertSorted(x: int, s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + InsertSorted(x, s[1..])
}

ghost function SortSeq(a: seq<int>): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else InsertSorted(a[|a| - 1], SortSeq(a[..|a| - 1]))
}

// Sum of consecutive-pair absolute differences:
// pairs (s[0],s[1]), (s[2],s[3]), ...
ghost function ConsecutivePairCost(s: seq<int>): int
  decreases |s|
{
  if |s| < 2 then 0
  else Abs(s[|s| - 1] - s[|s| - 2]) + ConsecutivePairCost(s[..|s| - 2])
}

// Minimum team-forming cost: sort then pair consecutively.
// This equals min { AssignmentCost(d) | ValidTeamAssignment(a, d, p) }
// over all valid (d, p), by the rearrangement inequality.
ghost function MinTeamCost(a: seq<int>): int {
  ConsecutivePairCost(SortSeq(a))
}

method TeamsForming(a: seq<int>) returns (ans: int)
  requires |a| % 2 == 0
  ensures ans >= 0
  ensures ans == MinTeamCost(a)
{
  var n := |a|;
  var arr := new int[n];
  var k := 0;
  while k < n {
    arr[k] := a[k];
    k := k + 1;
  }

  // Bubble sort
  var i := 0;
  while i < n {
    var j := 0;
    while j < n - 1 - i {
      if arr[j] > arr[j + 1] {
        var tmp := arr[j];
        arr[j] := arr[j + 1];
        arr[j + 1] := tmp;
      }
      j := j + 1;
    }
    i := i + 1;
  }

  // Sum differences of consecutive pairs
  ans := 0;
  i := 0;
  while i < n {
    ans := ans + arr[i + 1] - arr[i];
    i := i + 2;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0026_1092_B/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0026_1092_B/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0026_1092_B/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0026_1092_B/ (create the directory if needed).
