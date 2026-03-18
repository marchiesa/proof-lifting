Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Common Subsequence
You are given two arrays of integers $$$a_1,\ldots,a_n$$$ and $$$b_1,\ldots,b_m$$$.

Your task is to find a non-empty array $$$c_1,\ldots,c_k$$$ that is a subsequence of $$$a_1,\ldots,a_n$$$, and also a subsequence of $$$b_1,\ldots,b_m$$$. If there are multiple answers, find one of the smallest possible length. If there are still multiple of the smallest possible length, find any. If there are no such arrays, you should report about it.

A sequence $$$a$$$ is a subsequence of a sequence $$$b$$$ if $$$a$$$ can be obtained from $$$b$$$ by deletion of several (possibly, zero) elements. For example, $$$[3,1]$$$ is a subsequence of $$$[3,2,1]$$$ and $$$[4,3,1]$$$, but not a subsequence of $$$[1,3,3,7]$$$ and $$$[3,10,4]$$$.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0122_1382_A/task.dfy

```dafny
ghost predicate IsSubsequence(c: seq<int>, s: seq<int>)
  decreases |s|
{
  if |c| == 0 then true
  else if |s| == 0 then false
  else if c[|c|-1] == s[|s|-1] then IsSubsequence(c[..|c|-1], s[..|s|-1])
  else IsSubsequence(c, s[..|s|-1])
}

ghost predicate ExistsCommonSubseqOfLen(a: seq<int>, b: seq<int>, k: nat)
  decreases |a| + |b|
{
  if k == 0 then true
  else if |a| == 0 || |b| == 0 then false
  else if a[|a|-1] == b[|b|-1] then
    ExistsCommonSubseqOfLen(a[..|a|-1], b[..|b|-1], k - 1) ||
    ExistsCommonSubseqOfLen(a[..|a|-1], b, k) ||
    ExistsCommonSubseqOfLen(a, b[..|b|-1], k)
  else
    ExistsCommonSubseqOfLen(a[..|a|-1], b, k) ||
    ExistsCommonSubseqOfLen(a, b[..|b|-1], k)
}

ghost function Min(x: nat, y: nat): nat {
  if x <= y then x else y
}

method CommonSubsequence(a: seq<int>, b: seq<int>) returns (found: bool, c: seq<int>)
  ensures found ==>
    |c| >= 1 &&
    IsSubsequence(c, a) &&
    IsSubsequence(c, b) &&
    forall len :: 1 <= len < |c| ==> !ExistsCommonSubseqOfLen(a, b, len)
  ensures !found ==>
    forall len :: 1 <= len <= Min(|a|, |b|) ==> !ExistsCommonSubseqOfLen(a, b, len)
{
  found := false;
  c := [];
  var i := 0;
  while i < |a|
  {
    var j := 0;
    while j < |b|
    {
      if a[i] == b[j] {
        found := true;
        c := [a[i]];
        return;
      }
      j := j + 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0122_1382_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0122_1382_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0122_1382_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0122_1382_A/ (create the directory if needed).
