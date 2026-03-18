method EshagLovesBigArrays(a: seq<int>) returns (deleted: int)
{
  var mi := a[0];
  var i := 1;
  while i < |a|
  {
    if a[i] < mi {
      mi := a[i];
    }
    i := i + 1;
  }

  var c := 0;
  i := 0;
  while i < |a|
  {
    if a[i] == mi {
      c := c + 1;
    }
    i := i + 1;
  }

  deleted := |a| - c;
}

method Main()
{
  var result: int;

  // Test 1
  result := EshagLovesBigArrays([1, 1, 1, 2, 2, 3]);
  expect result == 3, "Test 1a failed";

  result := EshagLovesBigArrays([9, 9, 9, 9, 9, 9]);
  expect result == 0, "Test 1b failed";

  result := EshagLovesBigArrays([6, 4, 1, 1, 4, 1]);
  expect result == 3, "Test 1c failed";

  // Test 2
  result := EshagLovesBigArrays([1, 2]);
  expect result == 1, "Test 2 failed";

  // Test 3
  result := EshagLovesBigArrays([5]);
  expect result == 0, "Test 3 failed";

  // Test 4
  result := EshagLovesBigArrays([1, 1, 1, 1, 1]);
  expect result == 0, "Test 4 failed";

  // Test 5
  result := EshagLovesBigArrays([1, 2, 3]);
  expect result == 2, "Test 5 failed";

  // Test 6
  result := EshagLovesBigArrays([1, 1, 1, 2, 2, 3]);
  expect result == 3, "Test 6 failed";

  // Test 7
  result := EshagLovesBigArrays([3, 3, 3, 3]);
  expect result == 0, "Test 7 failed";

  // Test 8
  result := EshagLovesBigArrays([1, 2, 3, 4, 5, 6, 7]);
  expect result == 6, "Test 8 failed";

  // Test 9
  result := EshagLovesBigArrays([1, 50]);
  expect result == 1, "Test 9 failed";

  // Test 10
  result := EshagLovesBigArrays([1, 1, 2]);
  expect result == 1, "Test 10a failed";

  result := EshagLovesBigArrays([5, 5, 5, 10]);
  expect result == 1, "Test 10b failed";

  result := EshagLovesBigArrays([1, 1]);
  expect result == 0, "Test 10c failed";

  // Test 11
  result := EshagLovesBigArrays([1, 1, 1, 1, 1, 1, 1, 1, 1, 50]);
  expect result == 1, "Test 11 failed";

  // Test 12
  result := EshagLovesBigArrays([2, 2, 2, 2, 3]);
  expect result == 1, "Test 12a failed";

  result := EshagLovesBigArrays([6, 4, 1, 1, 4, 1]);
  expect result == 3, "Test 12b failed";

  print "All tests passed\n";
}