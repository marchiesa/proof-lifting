Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Non-zero
Guy-Manuel and Thomas have an array $$$a$$$ of $$$n$$$ integers [$$$a_1, a_2, \dots, a_n$$$]. In one step they can add $$$1$$$ to any element of the array. Formally, in one step they can choose any integer index $$$i$$$ ($$$1 \le i \le n$$$) and do $$$a_i := a_i + 1$$$.

If either the sum or the product of all elements in the array is equal to zero, Guy-Manuel and Thomas do not mind to do this operation one more time.

What is the minimum number of steps they need to do to make both the sum and the product of all elements in the array different from zero? Formally, find the minimum number of steps to make $$$a_1 + a_2 +$$$ $$$\dots$$$ $$$+ a_n \ne 0$$$ and $$$a_1 \cdot a_2 \cdot$$$ $$$\dots$$$ $$$\cdot a_n \ne 0$$$.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0090_1300_A/task.dfy

```dafny
ghost function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0
  else Sum(a[..|a|-1]) + a[|a|-1]
}

ghost function Product(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 1
  else Product(a[..|a|-1]) * a[|a|-1]
}

// Can exactly `budget` non-negative increments be distributed across `a`
// so that no element becomes zero (i.e., product of result is non-zero)?
ghost predicate CanDistribute(a: seq<int>, budget: nat)
  decreases |a|
{
  if |a| == 0 then
    budget == 0
  else
    exists d | 0 <= d <= budget ::
      a[|a|-1] + d != 0 &&
      CanDistribute(a[..|a|-1], budget - d)
}

// Can `budget` add-1 steps make both sum and product non-zero?
// Sum after modification is always Sum(a) + budget (independent of distribution).
// Product is non-zero iff CanDistribute finds a valid distribution avoiding zeros.
ghost predicate Feasible(a: seq<int>, budget: nat)
{
  Sum(a) + budget != 0 &&
  CanDistribute(a, budget)
}

method NonZero(a: seq<int>) returns (steps: int)
  requires |a| > 0
  ensures steps >= 0
  ensures Feasible(a, steps as nat)
  ensures forall k | 0 <= k < steps :: !Feasible(a, k as nat)
{
  var s := 0;
  var z := 0;
  var i := 0;
  while i < |a|
  {
    s := s + a[i];
    if a[i] == 0 {
      z := z + 1;
    }
    i := i + 1;
  }
  if s + z == 0 {
    return z + 1;
  } else {
    return z;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0090_1300_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0090_1300_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0090_1300_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0090_1300_A/ (create the directory if needed).
