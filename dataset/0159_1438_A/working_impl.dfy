method PerfectArray(n: int) returns (a: seq<int>)
{
  a := [];
  var i := 0;
  while i < n
  {
    a := a + [1];
    i := i + 1;
  }
}

method RepeatOne(n: int) returns (s: seq<int>)
{
  s := [];
  var i := 0;
  while i < n
  {
    s := s + [1];
    i := i + 1;
  }
}

method Main()
{
  var result: seq<int>;
  var expected: seq<int>;

  // Test 1: t=3, n=1,2,4
  result := PerfectArray(1);
  expected := RepeatOne(1);
  expect result == expected, "Test 1a failed: n=1";

  result := PerfectArray(2);
  expected := RepeatOne(2);
  expect result == expected, "Test 1b failed: n=2";

  result := PerfectArray(4);
  expected := RepeatOne(4);
  expect result == expected, "Test 1c failed: n=4";

  // Test 3: t=1, n=5
  result := PerfectArray(5);
  expected := RepeatOne(5);
  expect result == expected, "Test 3 failed: n=5";

  // Test 4: t=2, n=1,2 (already covered by Test 1)

  // Test 5: t=3, n=3,1,4
  result := PerfectArray(3);
  expected := RepeatOne(3);
  expect result == expected, "Test 5 failed: n=3";

  // Test 6: t=4, n=1,2,3,4 (all covered)

  // Test 7: t=5, n=10,20,30,40,50
  result := PerfectArray(10);
  expected := RepeatOne(10);
  expect result == expected, "Test 7a failed: n=10";

  result := PerfectArray(20);
  expected := RepeatOne(20);
  expect result == expected, "Test 7b failed: n=20";

  result := PerfectArray(30);
  expected := RepeatOne(30);
  expect result == expected, "Test 7c failed: n=30";

  result := PerfectArray(40);
  expected := RepeatOne(40);
  expect result == expected, "Test 7d failed: n=40";

  result := PerfectArray(50);
  expected := RepeatOne(50);
  expect result == expected, "Test 7e failed: n=50";

  // Test 8: t=1, n=1 (covered)

  // Test 9: t=6, n=1,1,1,1,1,1 (covered)

  // Test 10: t=3, n=50,49,48
  result := PerfectArray(49);
  expected := RepeatOne(49);
  expect result == expected, "Test 10 failed: n=49";

  result := PerfectArray(48);
  expected := RepeatOne(48);
  expect result == expected, "Test 10 failed: n=48";

  // Test 11: t=7, n=2,4,6,8,10,3,5
  result := PerfectArray(6);
  expected := RepeatOne(6);
  expect result == expected, "Test 11 failed: n=6";

  result := PerfectArray(8);
  expected := RepeatOne(8);
  expect result == expected, "Test 11 failed: n=8";

  result := PerfectArray(7);
  expected := RepeatOne(7);
  expect result == expected, "Test 11 failed: n=7";

  // Test 12: t=10, n=1..10
  result := PerfectArray(9);
  expected := RepeatOne(9);
  expect result == expected, "Test 12 failed: n=9";

  // Test 2: t=100, n=1..100 (covers all above and more)
  var n := 1;
  while n <= 100
  {
    result := PerfectArray(n);
    expected := RepeatOne(n);
    expect result == expected, "Test 2 failed: n=1..100";
    n := n + 1;
  }

  print "All tests passed\n";
}