ghost function Sum(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else Sum(s[..|s|-1]) + s[|s|-1]
}

ghost predicate AllNonNeg(s: seq<int>)
{
  forall i | 0 <= i < |s| :: s[i] >= 0
}

// Checks whether we can transport exactly `extra` additional haybales to pile 0
// by selecting haybales from `piles`, where piles[i] sits at distance (i+1) from
// pile 0, using at most `budget` total adjacent-pile moves. Each haybale at
// distance k costs exactly k moves to reach pile 0.
ghost predicate CanAchieveExtra(piles: seq<int>, budget: int, extra: int)
  decreases |piles|
{
  if extra < 0 || budget < 0 then false
  else if |piles| == 0 then extra == 0
  else
    exists take | 0 <= take <= piles[|piles| - 1] ::
      take * |piles| <= budget
      && CanAchieveExtra(piles[..|piles| - 1], budget - take * |piles|, extra - take)
}

// The result equals a[0] plus the maximum number of haybales transportable
// to pile 0 from the remaining piles within d adjacent-move operations.
ghost predicate IsOptimal(a: seq<int>, d: int, result: int)
  requires |a| > 0
{
  var piles := a[1..];
  var extra := result - a[0];
  var maxExtra := Sum(piles);
  0 <= extra
  && CanAchieveExtra(piles, d, extra)
  && (forall v | extra < v <= maxExtra :: !CanAchieveExtra(piles, d, v))
}

method CowAndHaybales(a: seq<int>, d: int) returns (result: int)
  requires |a| > 0
  requires d >= 0
  requires AllNonNeg(a)
  ensures IsOptimal(a, d, result)
{
  var n := |a|;
  var arr := new int[n];
  var Asum := 0;
  for k := 0 to n {
    arr[k] := a[k];
    Asum := Asum + a[k];
  }
  var remaining := d;
  while remaining > 0 && arr[0] != Asum
    decreases remaining
  {
    var i := 1;
    while i < n && arr[i] == 0
      decreases n - i
    {
      i := i + 1;
    }
    if i < n {
      arr[i - 1] := arr[i - 1] + 1;
      arr[i] := arr[i] - 1;
    }
    remaining := remaining - 1;
  }
  result := arr[0];
}