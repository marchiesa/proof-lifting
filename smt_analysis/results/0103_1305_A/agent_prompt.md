Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Kuroni and the Gifts
Kuroni has $$$n$$$ daughters. As gifts for them, he bought $$$n$$$ necklaces and $$$n$$$ bracelets:

- the $$$i$$$-th necklace has a brightness $$$a_i$$$, where all the $$$a_i$$$ are pairwise distinct (i.e. all $$$a_i$$$ are different),
- the $$$i$$$-th bracelet has a brightness $$$b_i$$$, where all the $$$b_i$$$ are pairwise distinct (i.e. all $$$b_i$$$ are different).

Kuroni wants to give exactly one necklace and exactly one bracelet to each of his daughters. To make sure that all of them look unique, the total brightnesses of the gifts given to each daughter should be pairwise distinct. Formally, if the $$$i$$$-th daughter receives a necklace with brightness $$$x_i$$$ and a bracelet with brightness $$$y_i$$$, then the sums $$$x_i + y_i$$$ should be pairwise distinct. Help Kuroni to distribute the gifts.

For example, if the brightnesses are $$$a = [1, 7, 5]$$$ and $$$b = [6, 1, 2]$$$, then we may distribute the gifts as follows:

- Give the third necklace and the first bracelet to the first daughter, for a total brightness of $$$a_3 + b_1 = 11$$$.
- Give the first necklace and the third bracelet to the second daughter, for a total brightness of $$$a_1 + b_3 = 3$$$.
- Give the second necklace and the second bracelet to the third daughter, for a total brightness of $$$a_2 + b_2 = 8$$$.

Here is an example of an invalid distribution:

- Give the first necklace and the first bracelet to the first daughter, for a total brightness of $$$a_1 + b_1 = 7$$$.
- Give the second necklace and the second bracelet to the second daughter, for a total brightness of $$$a_2 + b_2 = 8$$$.
- Give the third necklace and the third bracelet to the third daughter, for a total brightness of $$$a_3 + b_3 = 7$$$.

This distribution is invalid, as the total brightnesses of the gifts received by the first and the third daughter are the same. Don't make them this upset!

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0103_1305_A/task.dfy

```dafny
// ---------------------------------------------------------------------------
// Specification predicates and functions
// ---------------------------------------------------------------------------

ghost predicate IsSorted(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] <= s[j]
}

ghost predicate PairwiseDistinct(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] != s[j]
}

ghost predicate IsPermutation(a: seq<int>, b: seq<int>)
{
  multiset(a) == multiset(b)
}

ghost function Sums(x: seq<int>, y: seq<int>): seq<int>
  requires |x| == |y|
  decreases |x|
{
  if |x| == 0 then []
  else Sums(x[..|x|-1], y[..|y|-1]) + [x[|x|-1] + y[|y|-1]]
}

// ---------------------------------------------------------------------------
// Methods with specification
// ---------------------------------------------------------------------------

method Insert(sorted: seq<int>, val: int) returns (result: seq<int>)
  requires IsSorted(sorted)
  ensures IsSorted(result)
  ensures IsPermutation(result, sorted + [val])
{
  var i := 0;
  while i < |sorted| && sorted[i] < val
  {
    i := i + 1;
  }
  result := sorted[..i] + [val] + sorted[i..];
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures IsSorted(sorted)
  ensures IsPermutation(sorted, s)
{
  sorted := [];
  var i := 0;
  while i < |s|
  {
    sorted := Insert(sorted, s[i]);
    i := i + 1;
  }
}

// Specification of the problem:
//   Given two length-n sequences with pairwise-distinct elements,
//   produce permutations x of a and y of b such that the elementwise
//   sums x[i] + y[i] are pairwise distinct.
method KuroniAndTheGifts(a: seq<int>, b: seq<int>) returns (x: seq<int>, y: seq<int>)
  requires |a| == |b|
  requires PairwiseDistinct(a)
  requires PairwiseDistinct(b)
  ensures |x| == |a|
  ensures |y| == |a|
  ensures IsPermutation(x, a)
  ensures IsPermutation(y, b)
  ensures PairwiseDistinct(Sums(x, y))
{
  x := SortSeq(a);
  y := SortSeq(b);
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0103_1305_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0103_1305_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0103_1305_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0103_1305_A/ (create the directory if needed).
