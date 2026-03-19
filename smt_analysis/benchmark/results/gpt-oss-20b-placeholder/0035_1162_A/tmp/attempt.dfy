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

// ===== Helper Lemmas =====

lemma OptimalAssignmentLength(n: int, h: int, restrictions: seq<(int, int, int)>)
  requires n >= 0
  ensures |OptimalAssignment(n, h, restrictions)| == n
  decreases n
{
  if n > 0 {
    OptimalAssignmentLength(n - 1, h, restrictions);
  }
}

lemma OptimalAssignmentIndex(n: int, h: int, restrictions: seq<(int, int, int)>, idx: int)
  requires n >= 0
  requires 0 <= idx < n
  ensures |OptimalAssignment(n, h, restrictions)| == n
  ensures OptimalAssignment(n, h, restrictions)[idx] == EffectiveCap(idx, h, restrictions)
  decreases n
{
  OptimalAssignmentLength(n, h, restrictions);
  if idx < n - 1 {
    OptimalAssignmentIndex(n - 1, h, restrictions, idx);
  } else {
    OptimalAssignmentLength(n - 1, h, restrictions);
  }
}

lemma EffectiveCapRange(pos: int, h: int, restrictions: seq<(int, int, int)>)
  requires h >= 0
  requires forall k | 0 <= k < |restrictions| :: restrictions[k].2 >= 0
  ensures 0 <= EffectiveCap(pos, h, restrictions) <= h
  decreases |restrictions|
{
  if |restrictions| > 0 {
    EffectiveCapRange(pos, h, restrictions[..|restrictions|-1]);
  }
}

lemma EffectiveCapStep(pos: int, h: int, restrictions: seq<(int, int, int)>, k: int)
  requires 0 <= k < |restrictions|
  ensures EffectiveCap(pos, h, restrictions[..k+1]) ==
    (if restrictions[k].0 - 1 <= pos < restrictions[k].1 &&
        restrictions[k].2 < EffectiveCap(pos, h, restrictions[..k])
     then restrictions[k].2
     else EffectiveCap(pos, h, restrictions[..k]))
{
  assert restrictions[..k+1][..k] == restrictions[..k];
}

lemma EffectiveCapMonotone(pos: int, h: int, restrictions: seq<(int, int, int)>)
  requires |restrictions| > 0
  ensures EffectiveCap(pos, h, restrictions) <= EffectiveCap(pos, h, restrictions[..|restrictions|-1])
{
}

lemma EffectiveCapRespectsRestriction(pos: int, h: int, restrictions: seq<(int, int, int)>, k: int)
  requires h >= 0
  requires 0 <= k < |restrictions|
  requires forall m | 0 <= m < |restrictions| :: restrictions[m].2 >= 0
  requires restrictions[k].0 - 1 <= pos < restrictions[k].1
  ensures EffectiveCap(pos, h, restrictions) <= restrictions[k].2
  decreases |restrictions|
{
  if |restrictions| > 1 && k < |restrictions| - 1 {
    EffectiveCapRespectsRestriction(pos, h, restrictions[..|restrictions|-1], k);
    EffectiveCapMonotone(pos, h, restrictions);
  }
}

lemma EffectiveCapTightest(pos: int, h: int, restrictions: seq<(int, int, int)>, v: int)
  requires 0 <= v <= h
  requires forall k | 0 <= k < |restrictions| ::
    restrictions[k].0 - 1 <= pos < restrictions[k].1 ==> v <= restrictions[k].2
  ensures v <= EffectiveCap(pos, h, restrictions)
  decreases |restrictions|
{
  if |restrictions| > 0 {
    EffectiveCapTightest(pos, h, restrictions[..|restrictions|-1], v);
  }
}

lemma ProfitAppend(s: seq<int>, x: int)
  ensures Profit(s + [x]) == Profit(s) + x * x
{
  var t := s + [x];
  assert t[..|t|-1] == s;
}

// ===== Main Method =====

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

  // Loop 1: Initialize all heights to h
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j | 0 <= j < i :: ans[j] == h
  {
    ans[i] := h;
    i := i + 1;
  }

  // Transition: EffectiveCap(j, h, []) == h
  assert restrictions[..0] == [];

  // Loop 2: Apply each restriction
  i := 0;
  while i < |restrictions|
    invariant 0 <= i <= |restrictions|
    invariant forall j | 0 <= j < n :: ans[j] == EffectiveCap(j, h, restrictions[..i])
  {
    var l := restrictions[i].0;
    var r := restrictions[i].1;
    var x := restrictions[i].2;
    var j := l - 1;

    while j < r
      invariant l - 1 <= j <= r
      invariant forall pos | 0 <= pos < n && !(l - 1 <= pos < r) ::
        ans[pos] == EffectiveCap(pos, h, restrictions[..i])
      invariant forall pos | 0 <= pos < n && l - 1 <= pos < j ::
        ans[pos] == EffectiveCap(pos, h, restrictions[..i+1])
      invariant forall pos | 0 <= pos < n && j <= pos < r ::
        ans[pos] == EffectiveCap(pos, h, restrictions[..i])
    {
      ghost var old_val := ans[j];
      EffectiveCapStep(j, h, restrictions, i);
      assert ans[j] == EffectiveCap(j, h, restrictions[..i+1]);
      if ans[j] > x {
        ans[j] := x;
      }
      j := j + 1;
    }

    // Unify: for positions outside [l-1, r), EffectiveCap is unchanged
    forall pos | 0 <= pos < n
      ensures ans[pos] == EffectiveCap(pos, h, restrictions[..i+1])
    {
      if !(l - 1 <= pos < r) {
        EffectiveCapStep(pos, h, restrictions, i);
      }
    }

    i := i + 1;
  }

  assert forall pos | 0 <= pos < n :: ans[pos] == EffectiveCap(pos, h, restrictions);
  assert ans[..] == OptimalAssignment(n, h, restrictions);

  // Prove ans[..] == OptimalAssignment(n, h, restrictions)
  ghost var opt := OptimalAssignment(n, h, restrictions);
  OptimalAssignmentLength(n, h, restrictions);

  forall j | 0 <= j < n
    ensures ans[..][j] == opt[j]
  {
    OptimalAssignmentIndex(n, h, restrictions, j);
  }
  assert ans[..] == opt;

  // Loop 3: Compute total profit
  ghost var savedAns := ans[..];
  var temp := 0;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant temp == Profit(ans[..i])
    invariant ans[..] == savedAns
  {
    ProfitAppend(ans[..i], ans[i]);
    assert temp == Profit(ans[..i]) + ans[i] * ans[i];
    temp := temp + ans[i] * ans[i];
    i := i + 1;
  }

  assert temp == Profit(ans[..]);
  maxProfit := temp;
  assert maxProfit == Profit(ans[..]);

  // Prove ensures 1: IsValidAssignment
  forall idx | 0 <= idx < n
    ensures 0 <= opt[idx] <= h
  {
    OptimalAssignmentIndex(n, h, restrictions, idx);
    EffectiveCapRange(idx, h, restrictions);
  }

  forall k | 0 <= k < |restrictions|
    ensures forall j | restrictions[k].0 - 1 <= j < restrictions[k].1 ::
      0 <= j < n ==> opt[j] <= restrictions[k].2
  {
    forall j | restrictions[k].0 - 1 <= j < restrictions[k].1
      ensures 0 <= j < n ==> opt[j] <= restrictions[k].2
    {
      if 0 <= j < n {
        OptimalAssignmentIndex(n, h, restrictions, j);
        EffectiveCapRespectsRestriction(j, h, restrictions, k);
      }
    }
  }

  // Prove ensures 3: EffectiveCap is the tightest upper bound
  forall idx, v | 0 <= idx < n && 0 <= v <= h &&
      (forall k | 0 <= k < |restrictions| ::
        restrictions[k].0 - 1 <= idx < restrictions[k].1 ==> v <= restrictions[k].2)
    ensures v <= EffectiveCap(idx, h, restrictions)
  {
    EffectiveCapTightest(idx, h, restrictions, v);
  }
}
