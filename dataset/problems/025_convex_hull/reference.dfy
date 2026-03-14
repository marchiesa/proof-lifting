// Convex Hull (Upper Hull via Monotone Chain) -- Reference solution with invariants

// Cross product of vectors (p1->p2) and (p1->p3)
function Cross(x1: int, y1: int, x2: int, y2: int, x3: int, y3: int): int
{
  (x2 - x1) * (y3 - y1) - (y2 - y1) * (x3 - x1)
}

// Compute the upper hull of points sorted by x-coordinate
method UpperHull(xs: seq<int>, ys: seq<int>) returns (hull: seq<int>)
  requires |xs| == |ys| >= 1
  ensures |hull| >= 1
  ensures forall i :: 0 <= i < |hull| ==> 0 <= hull[i] < |xs|
  ensures forall i, j :: 0 <= i < j < |hull| ==> hull[i] < hull[j]
{
  hull := [0];
  var i := 1;
  while i < |xs|
    invariant 1 <= i <= |xs|
    invariant |hull| >= 1
    invariant forall k :: 0 <= k < |hull| ==> 0 <= hull[k] < i
    invariant forall k, l :: 0 <= k < l < |hull| ==> hull[k] < hull[l]
    decreases |xs| - i
  {
    // Remove points that make a non-left turn
    while |hull| >= 2 &&
      Cross(xs[hull[|hull| - 2]], ys[hull[|hull| - 2]],
            xs[hull[|hull| - 1]], ys[hull[|hull| - 1]],
            xs[i], ys[i]) >= 0
      invariant |hull| >= 1
      invariant forall k :: 0 <= k < |hull| ==> 0 <= hull[k] < i
      invariant forall k, l :: 0 <= k < l < |hull| ==> hull[k] < hull[l]
      decreases |hull|
    {
      hull := hull[..|hull| - 1];
    }
    hull := hull + [i];
    i := i + 1;
  }
}
