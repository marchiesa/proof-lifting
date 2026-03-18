Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Omkar and Infinity Clock
Being stuck at home, Ray became extremely bored. To pass time, he asks Lord Omkar to use his time bending power: Infinity Clock! However, Lord Omkar will only listen to mortals who can solve the following problem:

You are given an array $$$a$$$ of $$$n$$$ integers. You are also given an integer $$$k$$$. Lord Omkar wants you to do $$$k$$$ operations with this array.

Define one operation as the following:

1. Set $$$d$$$ to be the maximum value of your array.
2. For every $$$i$$$ from $$$1$$$ to $$$n$$$, replace $$$a_{i}$$$ with $$$d-a_{i}$$$.

The goal is to predict the contents in the array after $$$k$$$ operations. Please help Ray determine what the final sequence will look like!

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0135_1392_B/task.dfy

```dafny
ghost function MaxOfSeq(a: seq<int>): int
  requires |a| > 0
  decreases |a|
{
  if |a| == 1 then a[0]
  else
    var rest := MaxOfSeq(a[..|a|-1]);
    if a[|a|-1] > rest then a[|a|-1] else rest
}

ghost function SubtractFromAll(d: int, a: seq<int>): (r: seq<int>)
  decreases |a|
  ensures |r| == |a|
{
  if |a| == 0 then []
  else SubtractFromAll(d, a[..|a|-1]) + [d - a[|a|-1]]
}

// One operation: set d = max(a), replace each a[i] with d - a[i]
ghost function OperationStep(a: seq<int>): (r: seq<int>)
  requires |a| > 0
  ensures |r| == |a|
{
  SubtractFromAll(MaxOfSeq(a), a)
}

// Apply the operation k times by recursive unfolding
ghost function ApplyOperations(a: seq<int>, k: nat): (r: seq<int>)
  requires |a| > 0
  decreases k
  ensures |r| == |a|
{
  if k == 0 then a
  else ApplyOperations(OperationStep(a), k - 1)
}

method OmkarAndInfinityClock(a: seq<int>, k: int) returns (result: seq<int>)
  requires k >= 0
  ensures |a| == 0 ==> result == []
  ensures |a| > 0 ==> result == ApplyOperations(a, k)
{
  var n := |a|;
  if n == 0 {
    result := [];
    return;
  }
  var l := a;
  var kk := k;
  if kk > 4 {
    kk := kk - 2 * ((kk - 5) / 2);
  }
  var i := 0;
  while i < kk
  {
    var d := l[0];
    var j := 1;
    while j < n
    {
      if l[j] > d {
        d := l[j];
      }
      j := j + 1;
    }
    var newL: seq<int> := [];
    j := 0;
    while j < n
    {
      newL := newL + [d - l[j]];
      j := j + 1;
    }
    l := newL;
    i := i + 1;
  }
  result := l;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0135_1392_B/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0135_1392_B/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0135_1392_B/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0135_1392_B/ (create the directory if needed).
