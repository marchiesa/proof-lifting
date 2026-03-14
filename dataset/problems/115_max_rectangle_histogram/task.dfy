// Maximum Rectangle in Histogram
// Task: Add loop invariants so that Dafny can verify this program.

function Min(a: int, b: int): int { if a <= b then a else b }

function RectArea(heights: seq<int>, i: int, j: int): int
  requires 0 <= i <= j < |heights|
{
  MinHeight(heights, i, j) * (j - i + 1)
}

function MinHeight(heights: seq<int>, i: int, j: int): int
  requires 0 <= i <= j < |heights|
  decreases j - i
{
  if i == j then heights[i]
  else Min(heights[i], MinHeight(heights, i + 1, j))
}

method MaxRectHistogram(heights: seq<int>) returns (maxArea: int)
  requires |heights| > 0
  requires forall i :: 0 <= i < |heights| ==> heights[i] >= 0
  ensures forall i, j :: 0 <= i <= j < |heights| ==> RectArea(heights, i, j) <= maxArea
  ensures exists i, j :: 0 <= i <= j < |heights| && RectArea(heights, i, j) == maxArea
{
  maxArea := RectArea(heights, 0, 0);
  var i := 0;
  while i < |heights|
  {
    var j := i;
    while j < |heights|
    {
      var a := RectArea(heights, i, j);
      if a > maxArea {
        maxArea := a;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
