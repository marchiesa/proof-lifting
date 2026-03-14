// Convex Hull (Graham Scan simplified - upper hull)
// Task: Add loop invariants so that Dafny can verify this program.
// Computes the upper hull of a set of points sorted by x-coordinate.

// Cross product of vectors (p1->p2) and (p1->p3)
function Cross(p1x: int, p1y: int, p2x: int, p2y: int, p3x: int, p3y: int): int
{
  (p2x - p1x) * (p3y - p1y) - (p2y - p1y) * (p3x - p1x)
}

// Points are sorted by x-coordinate
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
  {
    while |hull| >= 2 &&
          Cross(xs[hull[|hull| - 2]], ys[hull[|hull| - 2]],
                xs[hull[|hull| - 1]], ys[hull[|hull| - 1]],
                xs[i], ys[i]) >= 0
    {
      hull := hull[..|hull| - 1];
    }
    hull := hull + [i];
    i := i + 1;
  }
}
