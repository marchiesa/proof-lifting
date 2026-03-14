// Convex Hull (Upper Hull) -- Test cases

method {:axiom} UpperHull(xs: seq<int>, ys: seq<int>) returns (hull: seq<int>)
  requires |xs| == |ys| >= 1
  ensures |hull| >= 1
  ensures forall i :: 0 <= i < |hull| ==> 0 <= hull[i] < |xs|
  ensures forall i, j :: 0 <= i < j < |hull| ==> hull[i] < hull[j]

method TestTriangle()
{
  var xs := [0, 1, 2, 3];
  var ys := [0, 2, 1, 0];
  var hull := UpperHull(xs, ys);
  assert |hull| >= 1;
  assert hull[0] >= 0;
  assert hull[0] < 4;
}

method TestSinglePoint()
{
  var xs := [5];
  var ys := [3];
  var hull := UpperHull(xs, ys);
  assert |hull| >= 1;
  assert hull[0] == 0;
}

method TestTwoPoints()
{
  var xs := [0, 1];
  var ys := [0, 1];
  var hull := UpperHull(xs, ys);
  assert |hull| >= 1;
}

method TestCollinear()
{
  var xs := [0, 1, 2];
  var ys := [0, 0, 0];
  var hull := UpperHull(xs, ys);
  assert |hull| >= 1;
}
