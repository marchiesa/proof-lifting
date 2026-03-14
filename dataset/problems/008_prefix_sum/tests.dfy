// Prefix Sum -- Runtime spec tests

function Sum(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else a[lo] + Sum(a, lo + 1, hi)
}

method Main()
{
  // Test Sum function directly
  var a := [1, 2, 3, 4];
  expect Sum(a, 0, 4) == 10, "sum(0,4) of [1,2,3,4] should be 10";
  expect Sum(a, 0, 1) == 1, "sum(0,1) of [1,2,3,4] should be 1";
  expect Sum(a, 0, 2) == 3, "sum(0,2) of [1,2,3,4] should be 3";
  expect Sum(a, 0, 3) == 6, "sum(0,3) of [1,2,3,4] should be 6";
  expect Sum(a, 0, 0) == 0, "empty range sum should be 0";
  expect Sum(a, 2, 4) == 7, "sum(2,4) of [1,2,3,4] should be 7";
  expect Sum(a, 1, 3) == 5, "sum(1,3) should be 5";

  // Test with single element
  var b := [5];
  expect Sum(b, 0, 1) == 5, "sum of single element";
  expect Sum(b, 0, 0) == 0, "empty sum of single element array";

  // Test with empty
  var c: seq<int> := [];
  expect Sum(c, 0, 0) == 0, "sum of empty seq";

  // Test with negatives
  var d := [-1, 1, -1, 1];
  expect Sum(d, 0, 4) == 0, "alternating sum should be 0";
  expect Sum(d, 0, 1) == -1, "first element is -1";
  expect Sum(d, 0, 2) == 0, "-1+1=0";

  // Test prefix sum property: Sum(a, 0, i+1) gives running total
  expect Sum(a, 0, 1) == 1, "prefix sum at index 0";
  expect Sum(a, 0, 2) == 3, "prefix sum at index 1";
  expect Sum(a, 0, 3) == 6, "prefix sum at index 2";
  expect Sum(a, 0, 4) == 10, "prefix sum at index 3";

  print "All spec tests passed\n";
}
