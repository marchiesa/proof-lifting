// Maximum Rectangle in Histogram -- Test cases
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

method {:axiom} MaxRectHistogram(heights: seq<int>) returns (maxArea: int)
  requires |heights| > 0
  requires forall i :: 0 <= i < |heights| ==> heights[i] >= 0
  ensures forall i, j :: 0 <= i <= j < |heights| ==> RectArea(heights, i, j) <= maxArea
  ensures exists i, j :: 0 <= i <= j < |heights| && RectArea(heights, i, j) == maxArea

method TestSingle() {
  var r := MaxRectHistogram([5]);
  assert RectArea([5], 0, 0) == 5;
}

method TestUniform() {
  // [2, 2, 2] -> max area = 6 (width 3, height 2)
  var r := MaxRectHistogram([2, 2, 2]);
}

method TestMixed() {
  // [2, 1, 5, 6, 2, 3] -> max area = 10 (heights[2..3], min=5, width=2)
  var r := MaxRectHistogram([2, 1, 5, 6, 2, 3]);
}
