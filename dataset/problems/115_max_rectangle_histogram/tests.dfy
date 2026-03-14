// Maximum Rectangle in Histogram -- Runtime spec tests

function Min(a: int, b: int): int { if a <= b then a else b }

function MinHeight(heights: seq<int>, i: int, j: int): int
  requires 0 <= i <= j < |heights|
  decreases j - i
{
  if i == j then heights[i]
  else Min(heights[i], MinHeight(heights, i + 1, j))
}

function RectArea(heights: seq<int>, i: int, j: int): int
  requires 0 <= i <= j < |heights|
{
  MinHeight(heights, i, j) * (j - i + 1)
}

method Main()
{
  // MinHeight tests
  expect MinHeight([2, 1, 5, 6, 2, 3], 0, 0) == 2, "MinHeight single = 2";
  expect MinHeight([2, 1, 5, 6, 2, 3], 0, 1) == 1, "MinHeight [2,1] = 1";
  expect MinHeight([2, 1, 5, 6, 2, 3], 2, 3) == 5, "MinHeight [5,6] = 5";
  expect MinHeight([2, 1, 5, 6, 2, 3], 0, 5) == 1, "MinHeight all = 1";

  // RectArea tests: positive
  expect RectArea([5], 0, 0) == 5, "RectArea of single bar [5] = 5";
  expect RectArea([2, 2, 2], 0, 2) == 6, "RectArea [2,2,2] = 2*3 = 6";
  expect RectArea([2, 1, 5, 6, 2, 3], 2, 3) == 10, "RectArea [5,6] = 5*2 = 10";
  expect RectArea([2, 1, 5, 6, 2, 3], 2, 2) == 5, "RectArea [5] = 5";

  // RectArea: wider ranges
  expect RectArea([2, 1, 5, 6, 2, 3], 0, 5) == 6, "RectArea full = 1*6 = 6";
  expect RectArea([2, 1, 5, 6, 2, 3], 2, 5) == 8, "RectArea [5,6,2,3] = 2*4 = 8";

  // RectArea: negative tests
  expect RectArea([2, 1, 5, 6, 2, 3], 2, 3) != 12, "RectArea [5,6] != 6*2";
  expect RectArea([2, 1, 5, 6, 2, 3], 2, 3) != 11, "RectArea [5,6] != 11";

  // RectArea: uniform heights
  expect RectArea([3, 3, 3, 3], 0, 3) == 12, "RectArea [3,3,3,3] = 3*4 = 12";

  // RectArea: single tall bar
  expect RectArea([1, 10, 1], 1, 1) == 10, "RectArea single tall = 10";
  expect RectArea([1, 10, 1], 0, 2) == 3, "RectArea [1,10,1] = 1*3 = 3";

  // MinHeight: negative test
  expect MinHeight([2, 1, 5, 6, 2, 3], 2, 3) != 6, "MinHeight [5,6] != 6";

  print "All spec tests passed\n";
}
