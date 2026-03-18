Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Points in Segments
You are given a set of $$$n$$$ segments on the axis $$$Ox$$$, each segment has integer endpoints between $$$1$$$ and $$$m$$$ inclusive. Segments may intersect, overlap or even coincide with each other. Each segment is characterized by two integers $$$l_i$$$ and $$$r_i$$$ ($$$1 \le l_i \le r_i \le m$$$) — coordinates of the left and of the right endpoints.

Consider all integer points between $$$1$$$ and $$$m$$$ inclusive. Your task is to print all such points that don't belong to any segment. The point $$$x$$$ belongs to the segment $$$[l; r]$$$ if and only if $$$l \le x \le r$$$.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0036_1015_A/task.dfy

```dafny
ghost predicate PointInSegment(p: int, seg: (int, int))
{
  seg.0 <= p <= seg.1
}

ghost predicate PointCoveredByAny(p: int, segments: seq<(int, int)>)
{
  exists i | 0 <= i < |segments| :: PointInSegment(p, segments[i])
}

ghost predicate StrictlyIncreasing(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] < s[j]
}

method PointsInSegments(segments: seq<(int, int)>, m: int) returns (result: seq<int>)
  requires m >= 0
  requires forall i | 0 <= i < |segments| :: 1 <= segments[i].0 <= segments[i].1 <= m
  // Every output point is a valid point in [1, m] that is not covered by any segment
  ensures forall i | 0 <= i < |result| :: 1 <= result[i] <= m
  ensures forall i | 0 <= i < |result| :: !PointCoveredByAny(result[i], segments)
  // Every uncovered point in [1, m] appears in the result (completeness)
  ensures forall p | 1 <= p <= m :: !PointCoveredByAny(p, segments) ==>
    (exists j | 0 <= j < |result| :: result[j] == p)
  // Output is in strictly increasing order (implies no duplicates)
  ensures StrictlyIncreasing(result)
{
  var A := seq(m, (_: int) => true);
  var i := 0;
  while i < |segments| {
    var a := segments[i].0;
    var b := segments[i].1;
    var j := a - 1;
    while j < b {
      if 0 <= j < |A| {
        A := A[j := false];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := [];
  var k := 0;
  while k < m {
    if A[k] {
      result := result + [k + 1];
    }
    k := k + 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0036_1015_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0036_1015_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0036_1015_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0036_1015_A/ (create the directory if needed).
