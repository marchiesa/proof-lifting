Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Even Array
You are given an array $$$a[0 \ldots n-1]$$$ of length $$$n$$$ which consists of non-negative integers. Note that array indices start from zero.

An array is called good if the parity of each index matches the parity of the element at that index. More formally, an array is good if for all $$$i$$$ ($$$0 \le i \le n - 1$$$) the equality $$$i \bmod 2 = a[i] \bmod 2$$$ holds, where $$$x \bmod 2$$$ is the remainder of dividing $$$x$$$ by 2.

For example, the arrays [$$$0, 5, 2, 1$$$] and [$$$0, 17, 0, 3$$$] are good, and the array [$$$2, 4, 6, 7$$$] is bad, because for $$$i=1$$$, the parities of $$$i$$$ and $$$a[i]$$$ are different: $$$i \bmod 2 = 1 \bmod 2 = 1$$$, but $$$a[i] \bmod 2 = 4 \bmod 2 = 0$$$.

In one move, you can take any two elements of the array and swap them (these elements are not necessarily adjacent).

Find the minimum number of moves in which you can make the array $$$a$$$ good, or say that this is not possible.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0129_1367_B/task.dfy

```dafny
// A "good" array has matching parity between each index and its element.
ghost predicate IsGood(a: seq<int>)
{
  forall i | 0 <= i < |a| :: i % 2 == a[i] % 2
}

// Swap elements at positions p and q.
ghost function SwapElems(a: seq<int>, p: int, q: int): seq<int>
  requires 0 <= p < |a|
  requires 0 <= q < |a|
{
  a[p := a[q]][q := a[p]]
}

// Can we reach a good array from `a` using at most `steps` swaps?
ghost predicate ReachableGoodIn(a: seq<int>, steps: nat)
  decreases steps
{
  if steps == 0 then IsGood(a)
  else IsGood(a) || exists p: int, q: int | 0 <= p < q < |a| ::
    ReachableGoodIn(SwapElems(a, p, q), steps - 1)
}

method EvenArray(a: seq<int>) returns (result: int)
  requires forall i | 0 <= i < |a| :: a[i] >= 0
  ensures result == -1 || result >= 0
  // If non-negative, we can make the array good in exactly `result` swaps...
  ensures result >= 0 ==> ReachableGoodIn(a, result)
  // ...and not in fewer.
  ensures result >= 1 ==> !ReachableGoodIn(a, result - 1)
  // If -1, no sequence of swaps can make it good.
  // Bound: each swap fixes at most 2 bad positions, so |a|/2 swaps always suffice
  // when a solution exists. Thus unreachable in |a|/2 implies truly impossible.
  ensures result == -1 ==> !ReachableGoodIn(a, |a| / 2)
{
  // ... method body unchanged ...
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0129_1367_B/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0129_1367_B/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0129_1367_B/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0129_1367_B/ (create the directory if needed).
