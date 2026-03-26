method PrettyPermutation(n: int) returns (perm: seq<int>)
{
  if n % 2 == 0 {
    perm := [2, 1];
    var i := 4;
    while i <= n {
      perm := perm + [i, i - 1];
      i := i + 2;
    }
  } else {
    perm := [3, 1, 2];
    var i := 5;
    while i <= n {
      perm := perm + [i, i - 1];
      i := i + 2;
    }
  }
}

method ComputeExpected(n: int) returns (expected: seq<int>)
{
  if n % 2 == 0 {
    expected := [];
    var i := 0;
    while i < n {
      expected := expected + [i + 2, i + 1];
      i := i + 2;
    }
  } else {
    expected := [3, 1, 2];
    var i := 3;
    while i < n {
      expected := expected + [i + 2, i + 1];
      i := i + 2;
    }
  }
}

method Main()
{
  // Test 3: n=2
  var r := PrettyPermutation(2);
  expect r == [2, 1], "Test n=2 failed";

  // Test 4: n=3
  r := PrettyPermutation(3);
  expect r == [3, 1, 2], "Test n=3 failed";

  // Test 5: n=4
  r := PrettyPermutation(4);
  expect r == [2, 1, 4, 3], "Test n=4 failed";

  // Test 6: n=5
  r := PrettyPermutation(5);
  expect r == [3, 1, 2, 5, 4], "Test n=5 failed";

  // Test 10/12: n=6
  r := PrettyPermutation(6);
  expect r == [2, 1, 4, 3, 6, 5], "Test n=6 failed";

  // Test 11: n=7
  r := PrettyPermutation(7);
  expect r == [3, 1, 2, 5, 4, 7, 6], "Test n=7 failed";

  // Test 11: n=8
  r := PrettyPermutation(8);
  expect r == [2, 1, 4, 3, 6, 5, 8, 7], "Test n=8 failed";

  // Test 12: n=9
  r := PrettyPermutation(9);
  expect r == [3, 1, 2, 5, 4, 7, 6, 9, 8], "Test n=9 failed";

  // Test 7: n=10
  r := PrettyPermutation(10);
  expect r == [2, 1, 4, 3, 6, 5, 8, 7, 10, 9], "Test n=10 failed";

  // Test 12: n=11
  r := PrettyPermutation(11);
  expect r == [3, 1, 2, 5, 4, 7, 6, 9, 8, 11, 10], "Test n=11 failed";

  // Test 11: n=49
  r := PrettyPermutation(49);
  expect r == [3, 1, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48], "Test n=49 failed";

  // Test 8/11: n=50
  r := PrettyPermutation(50);
  expect r == [2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 12, 11, 14, 13, 16, 15, 18, 17, 20, 19, 22, 21, 24, 23, 26, 25, 28, 27, 30, 29, 32, 31, 34, 33, 36, 35, 38, 37, 40, 39, 42, 41, 44, 43, 46, 45, 48, 47, 50, 49], "Test n=50 failed";

  // Test 2: comprehensive n=2..100
  var n := 2;
  while n <= 100 {
    r := PrettyPermutation(n);
    var expected := ComputeExpected(n);
    expect r == expected;
    n := n + 1;
  }

  print "All tests passed\n";
}