Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Suits
A new delivery of clothing has arrived today to the clothing store. This delivery consists of $$$a$$$ ties, $$$b$$$ scarves, $$$c$$$ vests and $$$d$$$ jackets.

The store does not sell single clothing items — instead, it sells suits of two types:

- a suit of the first type consists of one tie and one jacket;
- a suit of the second type consists of one scarf, one vest and one jacket.

Each suit of the first type costs $$$e$$$ coins, and each suit of the second type costs $$$f$$$ coins.

Calculate the maximum possible cost of a set of suits that can be composed from the delivered clothing items. Note that one item cannot be used in more than one suit (though some items may be left unused).

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0076_1271_A/task.dfy

```dafny
// --- Specification: captures the suit allocation optimization problem ---

ghost function MinVal(x: int, y: int): int {
  if x <= y then x else y
}

ghost function MaxVal(x: int, y: int): int {
  if x >= y then x else y
}

// A valid allocation: x type-1 suits (tie + jacket), y type-2 suits (scarf + vest + jacket)
ghost predicate ValidAllocation(a: int, b: int, c: int, d: int, x: int, y: int) {
  x >= 0 && y >= 0 &&
  x <= a &&
  y <= b &&
  y <= c &&
  x + y <= d
}

// Revenue from an allocation
ghost function AllocationCost(x: int, y: int, e: int, f: int): int {
  x * e + y * f
}

// Given x type-1 suits, the revenue-maximizing number of type-2 suits
ghost function BestY(b: int, c: int, d: int, f: int, x: int): int
  requires 0 <= b && 0 <= c && 0 <= x <= d
{
  var maxY := MinVal(b, MinVal(c, d - x));
  if f >= 0 then maxY else 0
}

// Best revenue when making exactly x type-1 suits (with optimal type-2 count)
ghost function CostForX(b: int, c: int, d: int, e: int, f: int, x: int): int
  requires 0 <= b && 0 <= c && 0 <= x <= d
{
  AllocationCost(x, BestY(b, c, d, f, x), e, f)
}

// Maximum of CostForX over x in [lo..hi], divide-and-conquer for O(log n) stack depth
ghost function MaxCostRange(b: int, c: int, d: int, e: int, f: int, lo: int, hi: int): int
  requires 0 <= b && 0 <= c && 0 <= d
  requires 0 <= lo <= hi <= d
  decreases hi - lo
{
  if lo == hi then
    CostForX(b, c, d, e, f, lo)
  else
    var mid := lo + (hi - lo) / 2;
    MaxVal(
      MaxCostRange(b, c, d, e, f, lo, mid),
      MaxCostRange(b, c, d, e, f, mid + 1, hi)
    )
}

// The maximum revenue achievable from any valid suit allocation
ghost function OptimalSuitsCost(a: int, b: int, c: int, d: int, e: int, f: int): int
  requires 0 <= a && 0 <= b && 0 <= c && 0 <= d
{
  MaxCostRange(b, c, d, e, f, 0, MinVal(a, d))
}

// --- Methods with formal specification ---

method Min2(x: int, y: int) returns (m: int)
  ensures m == MinVal(x, y)
{
  if x < y { m := x; } else { m := y; }
}

method Min3(x: int, y: int, z: int) returns (m: int)
  ensures m == MinVal(x, MinVal(y, z))
{
  m := x;
  if y < m { m := y; }
  if z < m { m := z; }
}

method Suits(a: int, b: int, c: int, d: int, e: int, f: int) returns (maxCost: int)
  requires 0 <= a && 0 <= b && 0 <= c && 0 <= d
  requires 0 <= e && 0 <= f
  // Achievability: some valid allocation yields maxCost
  ensures exists x: int | 0 <= x <= MinVal(a, d) ::
    ValidAllocation(a, b, c, d, x, BestY(b, c, d, f, x)) &&
    AllocationCost(x, BestY(b, c, d, f, x), e, f) == maxCost
  // Optimality: no allocation of type-1 suits can beat maxCost
  // (CostForX already maximizes over type-2 suits for each x, so this bounds all pairs)
  ensures forall x: int | 0 <= x <= MinVal(a, d) ::
    CostForX(b, c, d, e, f, x) <= maxCost
  // Result equals the computed optimum
  ensures maxCost == OptimalSuitsCost(a, b, c, d, e, f)
{
  if e > f {
    var x := Min2(a, d);
    var newD := d - x;
    var m := Min3(b, c, newD);
    maxCost := x * e + m * f;
  } else {
    var x := Min3(b, c, d);
    var newD := d - x;
    var m := Min2(a, newD);
    maxCost := x * f + m * e;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0076_1271_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0076_1271_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0076_1271_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0076_1271_A/ (create the directory if needed).
