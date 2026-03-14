// Container With Most Water -- Reference solution with invariants

function Min(a: int, b: int): int
{
  if a <= b then a else b
}

function Area(heights: seq<int>, i: int, j: int): int
  requires 0 <= i < j < |heights|
{
  Min(heights[i], heights[j]) * (j - i)
}

method MaxWaterContainer(heights: seq<int>) returns (maxArea: int)
  requires |heights| >= 2
  requires forall i :: 0 <= i < |heights| ==> heights[i] >= 0
  ensures forall i, j :: 0 <= i < j < |heights| ==> Area(heights, i, j) <= maxArea
  ensures exists i, j :: 0 <= i < j < |heights| && Area(heights, i, j) == maxArea
{
  maxArea := Area(heights, 0, 1);
  ghost var bestI := 0;
  ghost var bestJ := 1;
  var i := 0;
  while i < |heights|
    invariant 0 <= i <= |heights|
    invariant 0 <= bestI < bestJ < |heights|
    invariant Area(heights, bestI, bestJ) == maxArea
    invariant forall p, q :: 0 <= p < i && p < q < |heights| ==> Area(heights, p, q) <= maxArea
    decreases |heights| - i
  {
    var j := i + 1;
    while j < |heights|
      invariant i + 1 <= j <= |heights|
      invariant 0 <= bestI < bestJ < |heights|
      invariant Area(heights, bestI, bestJ) == maxArea
      invariant forall p, q :: 0 <= p < i && p < q < |heights| ==> Area(heights, p, q) <= maxArea
      invariant forall q :: i < q < j ==> Area(heights, i, q) <= maxArea
      decreases |heights| - j
    {
      var a := Area(heights, i, j);
      if a > maxArea {
        maxArea := a;
        bestI := i;
        bestJ := j;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
