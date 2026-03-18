Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Tram
Linear Kingdom has exactly one tram line. It has n stops, numbered from 1 to n in the order of tram's movement. At the i-th stop ai passengers exit the tram, while bi passengers enter it. The tram is empty before it arrives at the first stop. Also, when the tram arrives at the last stop, all passengers exit so that it becomes empty.

Your task is to calculate the tram's minimum capacity such that the number of people inside the tram at any time never exceeds this capacity. Note that at each stop all exiting passengers exit before any entering passenger enters the tram.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0101_116_A/task.dfy

```dafny
ghost function Sum(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else Sum(s[..|s|-1]) + s[|s|-1]
}

// Occupancy after processing all stops described by a and b:
// total who boarded minus total who exited
ghost function Occupancy(a: seq<int>, b: seq<int>): int
  requires |a| == |b|
{
  Sum(b) - Sum(a)
}

// A capacity is valid if it is non-negative and never exceeded
// at any stop (after the first k stops, for every k from 1 to n)
ghost predicate IsValidCapacity(c: int, n: int, a: seq<int>, b: seq<int>)
  requires 0 <= n <= |a| && n <= |b|
{
  c >= 0 &&
  forall k | 1 <= k <= n :: Occupancy(a[..k], b[..k]) <= c
}

// The minimum capacity: valid, and no smaller value is valid
ghost predicate IsMinimumCapacity(c: int, n: int, a: seq<int>, b: seq<int>)
  requires 0 <= n <= |a| && n <= |b|
{
  IsValidCapacity(c, n, a, b) &&
  forall c' | 0 <= c' < c :: !IsValidCapacity(c', n, a, b)
}

method Tram(n: int, a: seq<int>, b: seq<int>) returns (capacity: int)
  requires 0 <= n <= |a| && n <= |b|
  ensures IsMinimumCapacity(capacity, n, a, b)
{
  var current := 0;
  capacity := 0;
  var i := 0;
  while i < n
  {
    current := current - a[i] + b[i];
    if current > capacity {
      capacity := current;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0101_116_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0101_116_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0101_116_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0101_116_A/ (create the directory if needed).
