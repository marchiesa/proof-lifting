// Largest Rectangle Under Histogram -- Test cases

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

method Main()
{
  // Test MinHeight
  expect MinHeight([2, 1, 5, 6], 0, 4) == 1, "Min of [2,1,5,6] is 1";
  expect MinHeight([2, 1, 5, 6], 2, 4) == 5, "Min of [5,6] is 5";

  // Test RectArea
  expect RectArea([2, 1, 5, 6], 2, 4) == 10, "Area [5,6] = 5*2 = 10";
  expect RectArea([2, 1, 5, 6], 0, 4) == 4, "Area [2,1,5,6] = 1*4 = 4";

  // Test that largest rect in [2,1,5,6,2,3] is 10 (heights 5,6)
  expect RectArea([2, 1, 5, 6, 2, 3], 2, 4) == 10, "Area [5,6] = 10";
  expect RectArea([2, 1, 5, 6, 2, 3], 0, 6) == 6, "Area all = 1*6 = 6";

  print "All spec tests passed\n";
}
