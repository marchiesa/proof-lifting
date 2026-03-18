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