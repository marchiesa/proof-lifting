Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Phoenix and Gold
Phoenix has collected $$$n$$$ pieces of gold, and he wants to weigh them together so he can feel rich. The $$$i$$$-th piece of gold has weight $$$w_i$$$. All weights are distinct. He will put his $$$n$$$ pieces of gold on a weight scale, one piece at a time.

The scale has an unusual defect: if the total weight on it is exactly $$$x$$$, it will explode. Can he put all $$$n$$$ gold pieces onto the scale in some order, without the scale exploding during the process? If so, help him find some possible order.

Formally, rearrange the array $$$w$$$ so that for each $$$i$$$ $$$(1 \le i \le n)$$$, $$$\sum\limits_{j = 1}^{i}w_j \ne x$$$.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0214_1515_A/task.dfy

```dafny
ghost function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

ghost predicate AllDistinct(a: seq<int>)
{
  forall i, j | 0 <= i < |a| && 0 <= j < |a| && i != j :: a[i] != a[j]
}

ghost predicate IsPermutation(a: seq<int>, b: seq<int>)
{
  multiset(a) == multiset(b)
}

// Verify that a specific placement order never causes the scale to show weight x
ghost predicate NoPrefixSumEquals(a: seq<int>, x: int)
{
  forall i | 1 <= i <= |a| :: Sum(a[..i]) != x
}

// Operational model of the placement process:
// Given pieces already on the scale (`placed`), can we place all `remaining`
// pieces one at a time — each time choosing which piece to place next —
// such that the scale's total never equals x?
ghost predicate CanComplete(placed: seq<int>, remaining: seq<int>, x: int)
  decreases |remaining|
{
  if |remaining| == 0 then
    true
  else
    // Try each remaining piece as the next one to place
    exists i | 0 <= i < |remaining| ::
      // Placing remaining[i] must not make the total equal x
      Sum(placed) + remaining[i] != x
      // And we can successfully place all pieces after this choice
      && CanComplete(
           placed + [remaining[i]],
           remaining[..i] + remaining[i+1..],
           x
         )
}

// Starting from an empty scale, can all pieces in w be placed
// one at a time without the total ever reaching x?
ghost predicate ExistsValidOrdering(w: seq<int>, x: int)
{
  CanComplete([], w, x)
}

method PhoenixAndGold(n: int, x: int, w: seq<int>) returns (possible: bool, order: seq<int>)
  requires n == |w|
  requires n >= 1
  requires AllDistinct(w)
  ensures possible <==> ExistsValidOrdering(w, x)
  ensures possible ==> IsPermutation(order, w) && NoPrefixSumEquals(order, x)
{
  var s := 0;
  var i := 0;
  while i < |w| {
    s := s + w[i];
    i := i + 1;
  }

  if s == x {
    possible := false;
    order := [];
    return;
  }

  possible := true;
  var ww := w;
  var remaining := x;
  order := [];

  i := 0;
  while i < n {
    if ww[|ww| - 1] == remaining {
      var a := ww[|ww| - 1];
      var b := ww[|ww| - 2];
      ww := ww[..|ww| - 2] + [a] + [b];
    }
    var y := ww[|ww| - 1];
    ww := ww[..|ww| - 1];
    remaining := remaining - y;
    order := order + [y];
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0214_1515_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0214_1515_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0214_1515_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0214_1515_A/ (create the directory if needed).
