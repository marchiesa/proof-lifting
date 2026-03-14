// Container With Most Water -- Runtime spec tests

function Min(a: int, b: int): int { if a <= b then a else b }

function Area(heights: seq<int>, i: int, j: int): int
  requires 0 <= i < j < |heights|
{ Min(heights[i], heights[j]) * (j - i) }

method Main()
{
  // Area: positive cases
  var h := [1, 8, 6, 2, 5, 4, 8, 3, 7];
  expect Area(h, 1, 8) == 49, "Area(h, 1, 8) = min(8,7)*7 = 49";
  expect Area(h, 0, 8) == 8, "Area(h, 0, 8) = min(1,7)*8 = 8";
  expect Area(h, 1, 6) == 40, "Area(h, 1, 6) = min(8,8)*5 = 40";

  // Area: simple cases
  expect Area([1, 1], 0, 1) == 1, "Area([1,1], 0, 1) = 1";
  expect Area([5, 5], 0, 1) == 5, "Area([5,5], 0, 1) = 5";
  expect Area([1, 100], 0, 1) == 1, "Area([1,100], 0, 1) = min(1,100)*1 = 1";

  // Area: negative tests
  expect Area(h, 1, 8) != 56, "Area(h, 1, 8) != 8*7 (should use min)";
  expect Area(h, 0, 1) != 8, "Area(h, 0, 1) = min(1,8)*1 = 1, not 8";
  expect Area(h, 0, 1) == 1, "Area(h, 0, 1) = 1";

  // Verify Area is symmetric in the sense of Min
  expect Area([3, 5, 3], 0, 1) == 3, "Area([3,5,3], 0, 1) = min(3,5)*1 = 3";
  expect Area([3, 5, 3], 0, 2) == 6, "Area([3,5,3], 0, 2) = min(3,3)*2 = 6";
  expect Area([3, 5, 3], 1, 2) == 3, "Area([3,5,3], 1, 2) = min(5,3)*1 = 3";

  // Zero height
  expect Area([0, 5], 0, 1) == 0, "Area with zero height is 0";

  print "All spec tests passed\n";
}
