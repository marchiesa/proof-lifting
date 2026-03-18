Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Specific Tastes of Andre
Andre has very specific tastes. Recently he started falling in love with arrays.

Andre calls an nonempty array $$$b$$$ good, if sum of its elements is divisible by the length of this array. For example, array $$$[2, 3, 1]$$$ is good, as sum of its elements — $$$6$$$ — is divisible by $$$3$$$, but array $$$[1, 1, 2, 3]$$$ isn't good, as $$$7$$$ isn't divisible by $$$4$$$.

Andre calls an array $$$a$$$ of length $$$n$$$ perfect if the following conditions hold:

- Every nonempty subarray of this array is good.
- For every $$$i$$$ ($$$1 \le i \le n$$$), $$$1 \leq a_i \leq 100$$$.

Given a positive integer $$$n$$$, output any perfect array of length $$$n$$$. We can show that for the given constraints such an array always exists.

An array $$$c$$$ is a subarray of an array $$$d$$$ if $$$c$$$ can be obtained from $$$d$$$ by deletion of several (possibly, zero or all) elements from the beginning and several (possibly, zero or all) elements from the end.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0159_1438_A/task.dfy

```dafny
ghost function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

ghost predicate IsGood(b: seq<int>)
{
  |b| > 0 && Sum(b) % |b| == 0
}

ghost predicate AllElementsInRange(a: seq<int>)
{
  forall i | 0 <= i < |a| :: 1 <= a[i] <= 100
}

ghost predicate AllSubarraysGood(a: seq<int>)
{
  forall i, j | 0 <= i < j <= |a| :: IsGood(a[i..j])
}

ghost predicate IsPerfect(a: seq<int>)
{
  |a| > 0 && AllElementsInRange(a) && AllSubarraysGood(a)
}

method PerfectArray(n: int) returns (a: seq<int>)
  requires n >= 1
  ensures |a| == n
  ensures IsPerfect(a)
{
  a := [];
  var i := 0;
  while i < n
  {
    a := a + [1];
    i := i + 1;
  }
}

method RepeatOne(n: int) returns (s: seq<int>)
{
  s := [];
  var i := 0;
  while i < n
  {
    s := s + [1];
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0159_1438_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0159_1438_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0159_1438_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0159_1438_A/ (create the directory if needed).
