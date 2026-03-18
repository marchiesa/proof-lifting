method RestorePermutation(n: int, a: seq<int>) returns (p: seq<int>)
{
  var seen: set<int> := {};
  p := [];
  for i := 0 to |a| {
    if a[i] !in seen {
      p := p + [a[i]];
      seen := seen + {a[i]};
    }
  }
}

method Main()
{
  var r: seq<int>;

  // Test 1
  r := RestorePermutation(2, [1,1,2,2]);
  expect r == [1,2], "Test 1 failed";

  // Test 2
  r := RestorePermutation(4, [1,3,1,4,3,4,2,2]);
  expect r == [1,3,4,2], "Test 2 failed";

  // Test 3
  r := RestorePermutation(5, [1,2,1,2,3,4,3,5,4,5]);
  expect r == [1,2,3,4,5], "Test 3 failed";

  // Test 4
  r := RestorePermutation(3, [1,2,3,1,2,3]);
  expect r == [1,2,3], "Test 4 failed";

  // Test 5
  r := RestorePermutation(4, [2,3,2,4,1,3,4,1]);
  expect r == [2,3,4,1], "Test 5 failed";

  // Test 6
  r := RestorePermutation(1, [1,1]);
  expect r == [1], "Test 6 failed";

  // Test 7
  r := RestorePermutation(4, [4,1,4,3,2,1,3,2]);
  expect r == [4,1,3,2], "Test 7 failed";

  // Test 8
  r := RestorePermutation(4, [2,2,4,4,3,3,1,1]);
  expect r == [2,4,3,1], "Test 8 failed";

  // Test 9
  r := RestorePermutation(5, [5,5,4,4,3,2,3,1,2,1]);
  expect r == [5,4,3,2,1], "Test 9 failed";

  // Test 10
  r := RestorePermutation(2, [1,2,1,2]);
  expect r == [1,2], "Test 10 failed";

  // Test 11
  r := RestorePermutation(10, [7,7,2,3,6,2,4,3,6,4,9,10,8,9,10,1,8,1,5,5]);
  expect r == [7,2,3,6,4,9,10,8,1,5], "Test 11 failed";

  // Test 12
  r := RestorePermutation(4, [4,4,3,3,2,2,1,1]);
  expect r == [4,3,2,1], "Test 12 failed";

  // Test 13
  r := RestorePermutation(6, [5,5,1,4,1,4,6,2,6,2,3,3]);
  expect r == [5,1,4,6,2,3], "Test 13 failed";

  // Test 14
  r := RestorePermutation(7, [1,1,4,4,7,7,2,2,5,6,3,5,6,3]);
  expect r == [1,4,7,2,5,6,3], "Test 14 failed";

  // Test 15
  r := RestorePermutation(5, [5,4,3,5,2,4,3,2,1,1]);
  expect r == [5,4,3,2,1], "Test 15 failed";

  // Test 16
  r := RestorePermutation(3, [3,3,1,1,2,2]);
  expect r == [3,1,2], "Test 16 failed";

  // Test 17
  r := RestorePermutation(10, [8,3,8,3,1,4,5,9,2,6,1,4,5,10,7,9,2,6,10,7]);
  expect r == [8,3,1,4,5,9,2,6,10,7], "Test 17 failed";

  // Test 18
  r := RestorePermutation(9, [4,4,8,8,9,7,9,7,3,3,5,5,6,6,2,2,1,1]);
  expect r == [4,8,9,7,3,5,6,2,1], "Test 18 failed";

  // Test 19
  r := RestorePermutation(9, [3,4,3,4,1,1,9,9,8,8,6,7,5,6,2,7,5,2]);
  expect r == [3,4,1,9,8,6,7,5,2], "Test 19 failed";

  // Test 20
  r := RestorePermutation(5, [5,5,3,4,3,1,4,1,2,2]);
  expect r == [5,3,4,1,2], "Test 20 failed";

  // Test 21
  r := RestorePermutation(9, [1,8,1,9,8,3,9,3,2,6,5,4,7,2,6,5,4,7]);
  expect r == [1,8,9,3,2,6,5,4,7], "Test 21 failed";

  // Test 22
  r := RestorePermutation(9, [8,3,8,3,5,5,2,2,6,6,7,7,1,9,4,1,9,4]);
  expect r == [8,3,5,2,6,7,1,9,4], "Test 22 failed";

  // Test 23
  r := RestorePermutation(10, [5,5,3,1,2,6,9,7,4,8,3,1,10,2,6,9,7,4,8,10]);
  expect r == [5,3,1,2,6,9,7,4,8,10], "Test 23 failed";

  // Test 24
  r := RestorePermutation(2, [2,1,2,1]);
  expect r == [2,1], "Test 24 failed";

  // Test 25
  r := RestorePermutation(6, [3,3,4,4,6,6,5,2,5,2,1,1]);
  expect r == [3,4,6,5,2,1], "Test 25 failed";

  // Test 26
  r := RestorePermutation(3, [3,1,3,1,2,2]);
  expect r == [3,1,2], "Test 26 failed";

  // Test 27
  r := RestorePermutation(5, [2,2,3,3,1,5,1,5,4,4]);
  expect r == [2,3,1,5,4], "Test 27 failed";

  // Test 28
  r := RestorePermutation(9, [2,2,8,3,8,3,4,5,7,4,9,6,5,7,1,9,6,1]);
  expect r == [2,8,3,4,5,7,9,6,1], "Test 28 failed";

  print "All tests passed\n";
}