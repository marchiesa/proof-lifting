// Convex Hull (Graham Scan simplified - upper hull) -- Reference solution with invariants

function Cross(p1x: int, p1y: int, p2x: int, p2y: int, p3x: int, p3y: int): int
{
  (p2x - p1x) * (p3y - p1y) - (p2y - p1y) * (p3x - p1x)
}

predicate SortedByX(xs: seq<int>)
{
  forall i, j :: 0 <= i < j < |xs| ==> xs[i] <= xs[j]
}

method UpperHull(xs: seq<int>, ys: seq<int>) returns (hull: seq<int>)
  requires |xs| == |ys|
  requires |xs| >= 2
  requires SortedByX(xs)
  ensures |hull| >= 2
  ensures forall i :: 0 <= i < |hull| ==> 0 <= hull[i] < |xs|
{
  hull := [0, 1];
  var i := 2;
  while i < |xs|
    invariant 2 <= i <= |xs|
    invariant |hull| >= 2
    invariant forall k :: 0 <= k < |hull| ==> 0 <= hull[k] < i
    invariant hull[|hull| - 1] == i - 1
    invariant hull[0] == 0
    decreases |xs| - i
  {
    while |hull| >= 2 &&
          Cross(xs[hull[|hull| - 2]], ys[hull[|hull| - 2]],
                xs[hull[|hull| - 1]], ys[hull[|hull| - 1]],
                xs[i], ys[i]) >= 0
      invariant |hull| >= 1
      invariant forall k :: 0 <= k < |hull| ==> 0 <= hull[k] < i
      invariant hull[0] == 0
      decreases |hull|
    {
      hull := hull[..|hull| - 1];
    }
    hull := hull + [i];
    // |hull| >= 2 because hull had >= 1 element before adding i
    i := i + 1;
  }
}
