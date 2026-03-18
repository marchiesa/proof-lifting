function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

predicate IsGood(b: seq<int>)
{
  |b| > 0 && Sum(b) % |b| == 0
}

predicate AllElementsInRange(a: seq<int>)
{
  forall i | 0 <= i < |a| :: 1 <= a[i] <= 100
}

predicate AllSubarraysGood(a: seq<int>)
{
  forall i, j | 0 <= i < j <= |a| :: IsGood(a[i..j])
}

predicate IsPerfect(a: seq<int>)
{
  |a| > 0 && AllElementsInRange(a) && AllSubarraysGood(a)
}

method PerfectArray(n: int) returns (a: seq<int>)
  requires n >= 1
  ensures |a| == n
  ensures IsPerfect(a)
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
  // ===== SPEC POSITIVE TESTS =====
  // Top-level ensures: |a| == n && IsPerfect(a)
  // Using small inputs (length 1-3)

  // From positive test 8 (n=1, correct=[1])
  expect |[1]| == 1, "spec positive 1a";
  expect IsPerfect([1]), "spec positive 1b";

  // From positive test 4 (n=2, correct=[1,1])
  expect |[1, 1]| == 2, "spec positive 2a";
  expect IsPerfect([1, 1]), "spec positive 2b";

  // From positive test 5 (n=3, correct=[1,1,1])
  expect |[1, 1, 1]| == 3, "spec positive 3a";
  expect IsPerfect([1, 1, 1]), "spec positive 3b";

  // From positive test 9 (n=1 repeated, correct=[1])
  expect |[1]| == 1, "spec positive 4a";
  expect IsPerfect([1]), "spec positive 4b";

  // From positive test 1 (n=1, correct=[1])
  expect IsPerfect([1]), "spec positive 5";

  // From positive test 1 (n=2, correct=[1,1])
  expect IsPerfect([1, 1]), "spec positive 6";

  // From positive test 6 (n=3, correct=[1,1,1])
  expect IsPerfect([1, 1, 1]), "spec positive 7";

  // ===== SPEC NEGATIVE TESTS =====
  // Wrong outputs have first element changed from 1 to 2.
  // For n=1, IsPerfect([2]) is true so those are scaled to n>=2.

  // From neg 5 (n=3, wrong=[2,1,1] exact)
  expect !IsPerfect([2, 1, 1]), "spec negative 1";

  // From neg 3 (n=5, scaled to n=2, wrong=[2,1])
  expect !IsPerfect([2, 1]), "spec negative 2";

  // From neg 7 (n=10, scaled to n=3, wrong=[2,1,1])
  expect !IsPerfect([2, 1, 1]), "spec negative 3";

  // From neg 10 (n=50, scaled to n=3, wrong=[2,1,1])
  expect !IsPerfect([2, 1, 1]), "spec negative 4";

  // From neg 1 (n=1 scaled to n=2, wrong=[2,1])
  expect !IsPerfect([2, 1]), "spec negative 5";

  // From neg 4 (n=1 scaled to n=2, wrong=[2,1])
  expect !IsPerfect([2, 1]), "spec negative 6";

  // From neg 8 (n=1 scaled to n=2, wrong=[2,1])
  expect !IsPerfect([2, 1]), "spec negative 7";

  // From neg 9 (n=1 scaled to n=2, wrong=[2,1])
  expect !IsPerfect([2, 1]), "spec negative 8";

  // From neg 2 (n=1 scaled to n=2, wrong=[2,1])
  expect !IsPerfect([2, 1]), "spec negative 9";

  // From neg 6 (n=1 scaled to n=3, wrong=[2,1,1])
  expect !IsPerfect([2, 1, 1]), "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====
  var result: seq<int>;
  var expected: seq<int>;

  // Test 1: t=3, n=1,2,4
  result := PerfectArray(1);
  expected := RepeatOne(1);
  expect result == expected, "impl test 1a failed: n=1";

  result := PerfectArray(2);
  expected := RepeatOne(2);
  expect result == expected, "impl test 1b failed: n=2";

  result := PerfectArray(4);
  expected := RepeatOne(4);
  expect result == expected, "impl test 1c failed: n=4";

  // Test 3: n=5
  result := PerfectArray(5);
  expected := RepeatOne(5);
  expect result == expected, "impl test 3 failed: n=5";

  // Test 4: n=1,2
  result := PerfectArray(1);
  expected := RepeatOne(1);
  expect result == expected, "impl test 4a failed: n=1";

  result := PerfectArray(2);
  expected := RepeatOne(2);
  expect result == expected, "impl test 4b failed: n=2";

  // Test 5: n=3,1,4
  result := PerfectArray(3);
  expected := RepeatOne(3);
  expect result == expected, "impl test 5a failed: n=3";

  result := PerfectArray(1);
  expected := RepeatOne(1);
  expect result == expected, "impl test 5b failed: n=1";

  result := PerfectArray(4);
  expected := RepeatOne(4);
  expect result == expected, "impl test 5c failed: n=4";

  // Test 6: n=1,2,3,4
  result := PerfectArray(3);
  expected := RepeatOne(3);
  expect result == expected, "impl test 6 failed: n=3";

  // Test 7: n=10,20,30,40,50
  result := PerfectArray(10);
  expected := RepeatOne(10);
  expect result == expected, "impl test 7a failed: n=10";

  result := PerfectArray(20);
  expected := RepeatOne(20);
  expect result == expected, "impl test 7b failed: n=20";

  result := PerfectArray(30);
  expected := RepeatOne(30);
  expect result == expected, "impl test 7c failed: n=30";

  result := PerfectArray(40);
  expected := RepeatOne(40);
  expect result == expected, "impl test 7d failed: n=40";

  result := PerfectArray(50);
  expected := RepeatOne(50);
  expect result == expected, "impl test 7e failed: n=50";

  // Test 8: n=1
  result := PerfectArray(1);
  expect result == [1], "impl test 8 failed: n=1";

  // Test 9: n=1 (x6)
  var k := 0;
  while k < 6
  {
    result := PerfectArray(1);
    expect result == [1], "impl test 9 failed: n=1";
    k := k + 1;
  }

  // Test 10: n=50,49,48
  result := PerfectArray(50);
  expected := RepeatOne(50);
  expect result == expected, "impl test 10a failed: n=50";

  result := PerfectArray(49);
  expected := RepeatOne(49);
  expect result == expected, "impl test 10b failed: n=49";

  result := PerfectArray(48);
  expected := RepeatOne(48);
  expect result == expected, "impl test 10c failed: n=48";

  // Test 11: n=2,4,6,8,10,3,5
  result := PerfectArray(6);
  expected := RepeatOne(6);
  expect result == expected, "impl test 11a failed: n=6";

  result := PerfectArray(8);
  expected := RepeatOne(8);
  expect result == expected, "impl test 11b failed: n=8";

  result := PerfectArray(7);
  expected := RepeatOne(7);
  expect result == expected, "impl test 11c failed: n=7";

  // Test 12: n=1..10
  result := PerfectArray(9);
  expected := RepeatOne(9);
  expect result == expected, "impl test 12 failed: n=9";

  // Test 2: n=1..100
  var n := 1;
  while n <= 100
  {
    result := PerfectArray(n);
    expected := RepeatOne(n);
    expect result == expected, "impl test 2 failed: n=1..100";
    n := n + 1;
  }

  print "All tests passed\n";
}