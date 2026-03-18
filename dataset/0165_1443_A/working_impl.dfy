method KidsSeating(n: int) returns (chairs: seq<int>)
{
  chairs := [];
  var i := 0;
  while i < n
  {
    chairs := chairs + [2 * i + 2 * n + 2];
    i := i + 1;
  }
}

method ExpectedChairs(n: int) returns (expected: seq<int>)
{
  expected := [];
  var start := 2 * (n + 1);
  var i := 0;
  while i < n
  {
    expected := expected + [start + 2 * i];
    i := i + 1;
  }
}

method Main()
{
  var result: seq<int>;
  var expected: seq<int>;

  // Test 1: n=2, n=3, n=4
  result := KidsSeating(2);
  expect result == [6, 8], "Test1: n=2 failed";

  result := KidsSeating(3);
  expect result == [8, 10, 12], "Test1: n=3 failed";

  result := KidsSeating(4);
  expect result == [10, 12, 14, 16], "Test1: n=4 failed";

  // Test 2: n=1 through 100
  var i := 1;
  while i <= 100
  {
    result := KidsSeating(i);
    expected := ExpectedChairs(i);
    expect result == expected, "Test2 failed";
    i := i + 1;
  }

  // Test 3: 100 times n=1, all output [4]
  i := 0;
  while i < 100
  {
    result := KidsSeating(1);
    expect result == [4], "Test3 failed";
    i := i + 1;
  }

  // Test 4: 100 times n=100
  expected := ExpectedChairs(100);
  i := 0;
  while i < 100
  {
    result := KidsSeating(100);
    expect result == expected, "Test4 failed";
    i := i + 1;
  }

  // Test 5: alternating n=2 and n=1, 100 times
  i := 0;
  while i < 100
  {
    if i % 2 == 0 {
      result := KidsSeating(2);
      expect result == [6, 8], "Test5: n=2 failed";
    } else {
      result := KidsSeating(1);
      expect result == [4], "Test5: n=1 failed";
    }
    i := i + 1;
  }

  // Test 6: n values [9,3,9,4,5,4,7,6,7]
  result := KidsSeating(9);
  expect result == [20, 22, 24, 26, 28, 30, 32, 34, 36], "Test6: n=9 (1) failed";

  result := KidsSeating(3);
  expect result == [8, 10, 12], "Test6: n=3 failed";

  result := KidsSeating(9);
  expect result == [20, 22, 24, 26, 28, 30, 32, 34, 36], "Test6: n=9 (2) failed";

  result := KidsSeating(4);
  expect result == [10, 12, 14, 16], "Test6: n=4 (1) failed";

  result := KidsSeating(5);
  expect result == [12, 14, 16, 18, 20], "Test6: n=5 failed";

  result := KidsSeating(4);
  expect result == [10, 12, 14, 16], "Test6: n=4 (2) failed";

  result := KidsSeating(7);
  expect result == [16, 18, 20, 22, 24, 26, 28], "Test6: n=7 (1) failed";

  result := KidsSeating(6);
  expect result == [14, 16, 18, 20, 22, 24], "Test6: n=6 failed";

  result := KidsSeating(7);
  expect result == [16, 18, 20, 22, 24, 26, 28], "Test6: n=7 (2) failed";

  print "All tests passed\n";
}