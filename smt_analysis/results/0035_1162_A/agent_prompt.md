Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Zoning Restrictions Again
You are planning to build housing on a street. There are $$$n$$$ spots available on the street on which you can build a house. The spots are labeled from $$$1$$$ to $$$n$$$ from left to right. In each spot, you can build a house with an integer height between $$$0$$$ and $$$h$$$.

In each spot, if a house has height $$$a$$$, you will gain $$$a^2$$$ dollars from it.

The city has $$$m$$$ zoning restrictions. The $$$i$$$-th restriction says that the tallest house from spots $$$l_i$$$ to $$$r_i$$$ (inclusive) must be at most $$$x_i$$$.

You would like to build houses to maximize your profit. Determine the maximum profit possible.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0035_1162_A/task.dfy

```dafny
// A height assignment is valid: all heights in [0, h] and all zoning restrictions satisfied
ghost predicate IsValidAssignment(a: seq<int>, n: int, h: int, restrictions: seq<(int, int, int)>)
  requires n >= 0
{
  |a| == n &&
  (forall i | 0 <= i < n :: 0 <= a[i] <= h) &&
  (forall k | 0 <= k < |restrictions| ::
    forall j | restrictions[k].0 - 1 <= j < restrictions[k].1 ::
      0 <= j < n ==> a[j] <= restrictions[k].2)
}

// Total profit: sum of squared heights
ghost function Profit(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0
  else Profit(a[..|a|-1]) + a[|a|-1] * a[|a|-1]
}

// Maximum allowed height at 0-indexed position i: min of h and all applicable restriction values
ghost function EffectiveCap(i: int, h: int, restrictions: seq<(int, int, int)>): int
  decreases |restrictions|
{
  if |restrictions| == 0 then h
  else
    var prev := EffectiveCap(i, h, restrictions[..|restrictions|-1]);
    var r := restrictions[|restrictions|-1];
    if r.0 - 1 <= i < r.1 && r.2 < prev then r.2
    else prev
}

// The profit-maximizing assignment: each position gets its maximum allowed height
ghost function OptimalAssignment(n: int, h: int, restrictions: seq<(int, int, int)>): seq<int>
  requires n >= 0
  decreases n
{
  if n == 0 then []
  else OptimalAssignment(n - 1, h, restrictions) + [EffectiveCap(n - 1, h, restrictions)]
}

method ZoningRestrictions(n: int, h: int, m: int, restrictions: seq<(int, int, int)>) returns (maxProfit: int)
  requires n >= 0
  requires h >= 0
  requires forall k | 0 <= k < |restrictions| ::
    1 <= restrictions[k].0 <= restrictions[k].1 <= n && restrictions[k].2 >= 0
  // The optimal assignment (each position at its max allowed height) is a valid assignment
  ensures IsValidAssignment(OptimalAssignment(n, h, restrictions), n, h, restrictions)
  // The method returns the profit of the optimal assignment
  ensures maxProfit == Profit(OptimalAssignment(n, h, restrictions))
  // The effective cap is the tightest upper bound at each position: any height in [0, h]
  // satisfying all applicable restrictions cannot exceed it. Since profit is a sum of
  // per-position squares (monotone), no valid assignment can achieve higher total profit.
  ensures forall i | 0 <= i < n ::
    forall v | 0 <= v <= h ::
      (forall k | 0 <= k < |restrictions| ::
        restrictions[k].0 - 1 <= i < restrictions[k].1 ==> v <= restrictions[k].2)
      ==> v <= EffectiveCap(i, h, restrictions)
{
  var ans := new int[n];
  var i := 0;
  while i < n {
    ans[i] := h;
    i := i + 1;
  }

  i := 0;
  while i < |restrictions| {
    var l := restrictions[i].0;
    var r := restrictions[i].1;
    var x := restrictions[i].2;
    var j := l - 1;
    while j < r {
      if ans[j] > x {
        ans[j] := x;
      }
      j := j + 1;
    }
    i := i + 1;
  }

  var temp := 0;
  i := 0;
  while i < n {
    temp := temp + ans[i] * ans[i];
    i := i + 1;
  }
  maxProfit := temp;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0035_1162_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0035_1162_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0035_1162_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0035_1162_A/ (create the directory if needed).
