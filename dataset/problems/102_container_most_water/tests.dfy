// Container With Most Water -- Test cases

function Min(a: int, b: int): int { if a <= b then a else b }

function Area(heights: seq<int>, i: int, j: int): int
  requires 0 <= i < j < |heights|
{ Min(heights[i], heights[j]) * (j - i) }

method {:axiom} MaxWaterContainer(heights: seq<int>) returns (maxArea: int)
  requires |heights| >= 2
  requires forall i :: 0 <= i < |heights| ==> heights[i] >= 0
  ensures forall i, j :: 0 <= i < j < |heights| ==> Area(heights, i, j) <= maxArea
  ensures exists i, j :: 0 <= i < j < |heights| && Area(heights, i, j) == maxArea

method TestBasic()
{
  var h := [1, 8, 6, 2, 5, 4, 8, 3, 7];
  var m := MaxWaterContainer(h);
  assert Area(h, 1, 8) == Min(8, 7) * 7 == 49;
  assert m >= 49;
}

method TestTwo()
{
  var h := [1, 1];
  var m := MaxWaterContainer(h);
  assert Area(h, 0, 1) == 1;
}
