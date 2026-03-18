Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Restore the Permutation by Merger
A permutation of length $$$n$$$ is a sequence of integers from $$$1$$$ to $$$n$$$ of length $$$n$$$ containing each number exactly once. For example, $$$[1]$$$, $$$[4, 3, 5, 1, 2]$$$, $$$[3, 2, 1]$$$ are permutations, and $$$[1, 1]$$$, $$$[0, 1]$$$, $$$[2, 2, 1, 4]$$$ are not.

There was a permutation $$$p[1 \dots n]$$$. It was merged with itself. In other words, let's take two instances of $$$p$$$ and insert elements of the second $$$p$$$ into the first maintaining relative order of elements. The result is a sequence of the length $$$2n$$$.

For example, if $$$p=[3, 1, 2]$$$ some possible results are: $$$[3, 1, 2, 3, 1, 2]$$$, $$$[3, 3, 1, 1, 2, 2]$$$, $$$[3, 1, 3, 1, 2, 2]$$$. The following sequences are not possible results of a merging: $$$[1, 3, 2, 1, 2, 3$$$], [$$$3, 1, 2, 3, 2, 1]$$$, $$$[3, 3, 1, 2, 2, 1]$$$.

For example, if $$$p=[2, 1]$$$ the possible results are: $$$[2, 2, 1, 1]$$$, $$$[2, 1, 2, 1]$$$. The following sequences are not possible results of a merging: $$$[1, 1, 2, 2$$$], [$$$2, 1, 1, 2]$$$, $$$[1, 2, 2, 1]$$$.

Your task is to restore the permutation $$$p$$$ by the given resulting sequence $$$a$$$. It is guaranteed that the answer exists and is unique.

You have to answer $$$t$$$ independent test cases.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0133_1385_B/task.dfy

```dafny
ghost predicate IsPermutation(p: seq<int>, n: int)
{
  n >= 1 &&
  |p| == n &&
  (forall i | 1 <= i <= n :: exists j | 0 <= j < n :: p[j] == i)
}

ghost predicate IsMerge(a: seq<int>, s1: seq<int>, s2: seq<int>)
  decreases |a|
{
  if |a| == 0 then
    |s1| == 0 && |s2| == 0
  else
    (|s1| > 0 && a[0] == s1[0] && IsMerge(a[1..], s1[1..], s2)) ||
    (|s2| > 0 && a[0] == s2[0] && IsMerge(a[1..], s1, s2[1..]))
}

method RestorePermutation(n: int, a: seq<int>) returns (p: seq<int>)
  requires n >= 1
  requires |a| == 2 * n
  requires forall i | 0 <= i < |a| :: 1 <= a[i] <= n
  ensures IsPermutation(p, n)
  ensures IsMerge(a, p, p)
{
  var seen: set<int> := {};
  p := [];
  for i := 0 to |a| {
    if a[i] !in seen {
      p := p + [a[i]];
      seen := seen + {a[i]};
    }
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0133_1385_B/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0133_1385_B/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0133_1385_B/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0133_1385_B/ (create the directory if needed).
