Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Meximization
You are given an integer $$$n$$$ and an array $$$a_1, a_2, \ldots, a_n$$$. You should reorder the elements of the array $$$a$$$ in such way that the sum of $$$\textbf{MEX}$$$ on prefixes ($$$i$$$-th prefix is $$$a_1, a_2, \ldots, a_i$$$) is maximized.

Formally, you should find an array $$$b_1, b_2, \ldots, b_n$$$, such that the sets of elements of arrays $$$a$$$ and $$$b$$$ are equal (it is equivalent to array $$$b$$$ can be found as an array $$$a$$$ with some reordering of its elements) and $$$\sum\limits_{i=1}^{n} \textbf{MEX}(b_1, b_2, \ldots, b_i)$$$ is maximized.

$$$\textbf{MEX}$$$ of a set of nonnegative integers is the minimal nonnegative integer such that it is not in the set.

For example, $$$\textbf{MEX}(\{1, 2, 3\}) = 0$$$, $$$\textbf{MEX}(\{0, 1, 2, 4, 5\}) = 3$$$.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0207_1497_A/task.dfy

```dafny
// --- Specification: models the problem structure independently of the algorithm ---

ghost function SeqToSet(s: seq<int>): set<int>
  decreases |s|
{
  if |s| == 0 then {} else SeqToSet(s[..|s|-1]) + {s[|s|-1]}
}

// Searches for the smallest nat >= k not in s, with fuel bounding the search depth.
// Since MEX(s) <= |s| by pigeonhole, fuel = |s| suffices when starting from k = 0.
ghost function MexSearch(s: set<int>, k: nat, fuel: nat): nat
  decreases fuel
{
  if fuel == 0 || k !in s then k
  else MexSearch(s, k + 1, fuel - 1)
}

// MEX of a set: the minimum non-negative integer not in the set.
ghost function Mex(s: set<int>): nat
{
  MexSearch(s, 0, |s|)
}

// Sum of MEX over all prefixes: sum_{i=1}^{|a|} MEX({a[0], ..., a[i-1]})
ghost function PrefixMexSum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0
  else PrefixMexSum(a[..|a|-1]) + Mex(SeqToSet(a))
}

// b is a rearrangement of a (same multiset of elements).
ghost predicate IsPermutation(a: seq<int>, b: seq<int>)
{
  multiset(a) == multiset(b)
}

ghost predicate IsSorted(s: seq<int>)
{
  forall i | 0 <= i < |s| - 1 :: s[i] <= s[i + 1]
}

// Enumerates all orderings of 'remaining' appended to 'chosen', and checks
// that every such complete sequence has PrefixMexSum <= target.
// This is the direct formalization of "no permutation beats the target sum".
ghost predicate NoBetterArrangement(target: int, chosen: seq<int>, remaining: seq<int>)
  decreases |remaining|
{
  if |remaining| == 0 then
    PrefixMexSum(chosen) <= target
  else
    forall i | 0 <= i < |remaining| ::
      NoBetterArrangement(
        target,
        chosen + [remaining[i]],
        remaining[..i] + remaining[i+1..]
      )
}

// --- Methods with formal specifications ---

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures IsPermutation(s, sorted)
  ensures IsSorted(sorted)
{
  var arr := s;
  for i := 1 to |arr| {
    var j := i;
    while j > 0 && arr[j - 1] > arr[j]
      decreases j
    {
      var tmp := arr[j];
      arr := arr[j := arr[j - 1]];
      arr := arr[j - 1 := tmp];
      j := j - 1;
    }
  }
  sorted := arr;
}

method Meximization(a: seq<int>) returns (b: seq<int>)
  ensures IsPermutation(a, b)
  ensures NoBetterArrangement(PrefixMexSum(b), [], a)
{
  var s: set<int> := {};
  var res: seq<int> := [];
  var ss: seq<int> := [];
  for i := 0 to |a| {
    var x := a[i];
    if x in s {
      ss := ss + [x];
    } else {
      res := res + [x];
    }
    s := s + {x};
  }
  res := SortSeq(res);
  b := res + ss;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0207_1497_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0207_1497_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0207_1497_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0207_1497_A/ (create the directory if needed).
