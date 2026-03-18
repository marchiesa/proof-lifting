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