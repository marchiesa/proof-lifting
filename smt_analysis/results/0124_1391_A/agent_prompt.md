Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Suborrays
A permutation of length $$$n$$$ is an array consisting of $$$n$$$ distinct integers from $$$1$$$ to $$$n$$$ in arbitrary order. For example, $$$[2,3,1,5,4]$$$ is a permutation, but $$$[1,2,2]$$$ is not a permutation ($$$2$$$ appears twice in the array) and $$$[1,3,4]$$$ is also not a permutation ($$$n=3$$$ but there is $$$4$$$ in the array).

For a positive integer $$$n$$$, we call a permutation $$$p$$$ of length $$$n$$$ good if the following condition holds for every pair $$$i$$$ and $$$j$$$ ($$$1 \le i \le j \le n$$$) —

- $$$(p_i \text{ OR } p_{i+1} \text{ OR } \ldots \text{ OR } p_{j-1} \text{ OR } p_{j}) \ge j-i+1$$$, where $$$\text{OR}$$$ denotes the bitwise OR operation.

In other words, a permutation $$$p$$$ is good if for every subarray of $$$p$$$, the $$$\text{OR}$$$ of all elements in it is not less than the number of elements in that subarray.

Given a positive integer $$$n$$$, output any good permutation of length $$$n$$$. We can show that for the given constraints such a permutation always exists.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0124_1391_A/task.dfy

```dafny
// --- Spec: Bitwise OR for non-negative integers ---
ghost function BitwiseOr(a: int, b: int): int
  requires a >= 0 && b >= 0
  ensures BitwiseOr(a, b) >= 0
  decreases a + b
{
  if a == 0 && b == 0 then 0
  else
    (if a % 2 == 1 || b % 2 == 1 then 1 else 0) + 2 * BitwiseOr(a / 2, b / 2)
}

// --- Spec: OR of all elements in a non-empty sequence ---
ghost function OrOfSeq(s: seq<int>): int
  requires |s| > 0
  requires forall i | 0 <= i < |s| :: s[i] >= 0
  ensures OrOfSeq(s) >= 0
  decreases |s|
{
  if |s| == 1 then s[0]
  else BitwiseOr(OrOfSeq(s[..|s|-1]), s[|s|-1])
}

// --- Spec: p is a permutation of [1..n] ---
ghost predicate IsPermutation(p: seq<int>, n: int)
{
  n >= 0 &&
  |p| == n &&
  (forall i | 0 <= i < n :: 1 <= p[i] <= n) &&
  (forall i, j | 0 <= i < j < n :: p[i] != p[j])
}

// --- Spec: every subarray's bitwise OR >= the subarray's length ---
ghost predicate IsGood(p: seq<int>)
{
  (forall k | 0 <= k < |p| :: p[k] >= 0) &&
  (forall i, j | 0 <= i <= j < |p| :: OrOfSeq(p[i..j+1]) >= j - i + 1)
}

method GoodPermutation(n: int) returns (p: seq<int>)
  requires n >= 1
  ensures IsPermutation(p, n)
  ensures IsGood(p)
{
  p := [];
  var i := 1;
  while i <= n
  {
    p := p + [i];
    i := i + 1;
  }
}

method ExpectedPermutation(n: int) returns (e: seq<int>)
{
  e := [];
  var i := 1;
  while i <= n
  {
    e := e + [i];
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0124_1391_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0124_1391_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0124_1391_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0124_1391_A/ (create the directory if needed).
