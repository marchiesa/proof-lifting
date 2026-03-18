Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Spy Detected!
You are given an array $$$a$$$ consisting of $$$n$$$ ($$$n \ge 3$$$) positive integers. It is known that in this array, all the numbers except one are the same (for example, in the array $$$[4, 11, 4, 4]$$$ all numbers except one are equal to $$$4$$$).

Print the index of the element that does not equal others. The numbers in the array are numbered from one.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0215_1512_A/task.dfy

```dafny
ghost function CountOccurrences(a: seq<int>, v: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else CountOccurrences(a[..|a|-1], v) + (if a[|a|-1] == v then 1 else 0)
}

ghost predicate IsMajorityValue(a: seq<int>, v: int)
{
  CountOccurrences(a, v) == |a| - 1
}

ghost predicate IsSpyIndex(a: seq<int>, idx: int)
{
  1 <= idx <= |a| &&
  exists k | 0 <= k < |a| :: IsMajorityValue(a, a[k]) && a[idx - 1] != a[k]
}

method SpyDetected(a: seq<int>) returns (idx: int)
  requires |a| >= 3
  requires forall i | 0 <= i < |a| :: a[i] > 0
  requires exists k | 0 <= k < |a| :: IsMajorityValue(a, a[k])
  ensures IsSpyIndex(a, idx)
{
  var i := 0;
  while i < |a|
  {
    var count := 0;
    var j := 0;
    while j < |a|
    {
      if a[j] == a[i] {
        count := count + 1;
      }
      j := j + 1;
    }
    if count == 1 {
      return i + 1;
    }
    i := i + 1;
  }
  return 0;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0215_1512_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0215_1512_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0215_1512_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0215_1512_A/ (create the directory if needed).
