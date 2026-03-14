// Convex Hull (Upper Hull) -- Test cases

method {:axiom} UpperHull(xs: seq<int>, ys: seq<int>) returns (hull: seq<int>)
  requires |xs| == |ys|
  requires |xs| >= 2
  requires forall i, j :: 0 <= i < j < |xs| ==> xs[i] <= xs[j]
  ensures |hull| >= 2
  ensures forall i :: 0 <= i < |hull| ==> 0 <= hull[i] < |xs|

method TestTwoPoints()
{
  var h := UpperHull([0, 1], [0, 1]);
  assert |h| >= 2;
  assert h[0] >= 0;
  assert h[0] < 2;
}

method TestThreeCollinear()
{
  var h := UpperHull([0, 1, 2], [0, 1, 2]);
  assert |h| >= 2;
}

method TestSquare()
{
  var h := UpperHull([0, 0, 1, 1], [0, 1, 0, 1]);
  assert |h| >= 2;
  assert forall i :: 0 <= i < |h| ==> 0 <= h[i] < 4;
}
