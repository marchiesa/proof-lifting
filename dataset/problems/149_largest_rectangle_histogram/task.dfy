// Largest Rectangle Under Histogram
// Task: Add loop invariants so that Dafny can verify this program.

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

method LargestRectangle(heights: seq<int>) returns (maxArea: int)
  requires |heights| > 0
  requires forall i :: 0 <= i < |heights| ==> heights[i] >= 0
  ensures maxArea >= 0
{
  maxArea := 0;
  var i := 0;
  while i < |heights|
  {
    var j := i + 1;
    while j <= |heights|
    {
      var area := RectArea(heights, i, j);
      if area > maxArea {
        maxArea := area;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
