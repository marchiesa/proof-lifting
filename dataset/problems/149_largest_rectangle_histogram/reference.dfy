// Largest Rectangle Under Histogram -- Reference solution with invariants

function Min(a: int, b: int): int { if a <= b then a else b }

function MinHeight(heights: seq<int>, lo: int, hi: int): int
  requires 0 <= lo < hi <= |heights|
  decreases hi - lo
{
  if hi - lo == 1 then heights[lo]
  else Min(heights[lo], MinHeight(heights, lo + 1, hi))
}

function RectArea(heights: seq<int>, lo: int, hi: int): int
  requires 0 <= lo < hi <= |heights|
{
  MinHeight(heights, lo, hi) * (hi - lo)
}

lemma MinHeightNonNeg(heights: seq<int>, lo: int, hi: int)
  requires 0 <= lo < hi <= |heights|
  requires forall i :: 0 <= i < |heights| ==> heights[i] >= 0
  ensures MinHeight(heights, lo, hi) >= 0
  decreases hi - lo
{
  if hi - lo > 1 { MinHeightNonNeg(heights, lo + 1, hi); }
}

lemma RectAreaNonNeg(heights: seq<int>, lo: int, hi: int)
  requires 0 <= lo < hi <= |heights|
  requires forall i :: 0 <= i < |heights| ==> heights[i] >= 0
  ensures RectArea(heights, lo, hi) >= 0
{
  MinHeightNonNeg(heights, lo, hi);
}

method LargestRectangle(heights: seq<int>) returns (maxArea: int)
  requires |heights| > 0
  requires forall i :: 0 <= i < |heights| ==> heights[i] >= 0
  ensures maxArea >= 0
{
  maxArea := 0;
  var i := 0;
  while i < |heights|
    invariant 0 <= i <= |heights|
    invariant maxArea >= 0
    decreases |heights| - i
  {
    var j := i + 1;
    while j <= |heights|
      invariant i + 1 <= j <= |heights| + 1
      invariant maxArea >= 0
      decreases |heights| + 1 - j
    {
      RectAreaNonNeg(heights, i, j);
      var area := RectArea(heights, i, j);
      if area > maxArea {
        maxArea := area;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
