method AverageHeight(a: seq<int>) returns (result: seq<int>)
{
  var odd: seq<int> := [];
  var even: seq<int> := [];
  var i := 0;
  while i < |a|
  {
    if a[i] % 2 != 0 {
      odd := odd + [a[i]];
    } else {
      even := even + [a[i]];
    }
    i := i + 1;
  }
  result := odd + even;
}

method Main()
{
  var r: seq<int>;

  // Test 1a
  r := AverageHeight([1, 1, 2]);
  expect r == [1, 1, 2], "Test 1a failed";

  // Test 1b
  r := AverageHeight([1, 1, 1]);
  expect r == [1, 1, 1], "Test 1b failed";

  // Test 1c
  r := AverageHeight([10, 9, 13, 15, 3, 16, 9, 13]);
  expect r == [9, 13, 15, 3, 9, 13, 10, 16], "Test 1c failed";

  // Test 1d
  r := AverageHeight([18, 9]);
  expect r == [9, 18], "Test 1d failed";

  // Test 2
  r := AverageHeight([1, 2]);
  expect r == [1, 2], "Test 2 failed";

  // Test 4
  r := AverageHeight([2, 4, 6, 8]);
  expect r == [2, 4, 6, 8], "Test 4 failed";

  // Test 5
  r := AverageHeight([1, 3, 5, 7, 9]);
  expect r == [1, 3, 5, 7, 9], "Test 5 failed";

  // Test 7
  r := AverageHeight([1, 2, 3, 4, 5, 6]);
  expect r == [1, 3, 5, 2, 4, 6], "Test 7 failed";

  // Test 8
  r := AverageHeight([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
  expect r == [1, 3, 5, 7, 9, 2, 4, 6, 8, 10], "Test 8 failed";

  // Test 9a
  r := AverageHeight([5, 10, 15]);
  expect r == [5, 15, 10], "Test 9a failed";

  // Test 9b
  r := AverageHeight([2, 2, 3, 3]);
  expect r == [3, 3, 2, 2], "Test 9b failed";

  // Test 10a
  r := AverageHeight([1, 1]);
  expect r == [1, 1], "Test 10a failed";

  // Test 10b
  r := AverageHeight([3, 3, 3]);
  expect r == [3, 3, 3], "Test 10b failed";

  print "All tests passed\n";
}