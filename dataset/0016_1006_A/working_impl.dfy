method AdjacentReplacements(a: seq<int>) returns (b: seq<int>)
{
  b := [];
  for i := 0 to |a| {
    if a[i] % 2 == 0 {
      b := b + [a[i] - 1];
    } else {
      b := b + [a[i]];
    }
  }
}

method Main()
{
  var result: seq<int>;

  // Test 1
  result := AdjacentReplacements([1, 2, 4, 5, 10]);
  expect result == [1, 1, 3, 5, 9], "Test 1 failed";

  // Test 2
  result := AdjacentReplacements([10000, 10, 50605065, 1, 5, 89, 5, 999999999, 60506056, 1000000000]);
  expect result == [9999, 9, 50605065, 1, 5, 89, 5, 999999999, 60506055, 999999999], "Test 2 failed";

  // Test 3
  result := AdjacentReplacements([999999999]);
  expect result == [999999999], "Test 3 failed";

  // Test 4
  result := AdjacentReplacements([1000000000]);
  expect result == [999999999], "Test 4 failed";

  // Test 5
  result := AdjacentReplacements([210400]);
  expect result == [210399], "Test 5 failed";

  // Test 6
  result := AdjacentReplacements([100000000, 100000000, 100000000, 100000000, 100000000]);
  expect result == [99999999, 99999999, 99999999, 99999999, 99999999], "Test 6 failed";

  // Test 7
  result := AdjacentReplacements([2441139]);
  expect result == [2441139], "Test 7 failed";

  // Test 8
  result := AdjacentReplacements([2, 2]);
  expect result == [1, 1], "Test 8 failed";

  // Test 9
  result := AdjacentReplacements([2, 2, 2]);
  expect result == [1, 1, 1], "Test 9 failed";

  // Test 10
  result := AdjacentReplacements([4, 4]);
  expect result == [3, 3], "Test 10 failed";

  print "All tests passed\n";
}