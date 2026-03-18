// --- Specification ---

function Gcd(a: int, b: int): int
  requires a > 0 && b > 0
  decreases a + b
{
  if a == b then a
  else if a > b then Gcd(a - b, b)
  else Gcd(a, b - a)
}

predicate WouldIndulge(a: int, b: int)
  requires a > 0 && b > 0
{
  Gcd(a, b) == 1 || a % b == 0 || b % a == 0
}

predicate ValidSeating(chairs: seq<int>, n: int)
{
  |chairs| == n
  && (forall i | 0 <= i < n :: 1 <= chairs[i] <= 4 * n)
  && (forall i, j | 0 <= i < n && 0 <= j < n && i != j :: chairs[i] != chairs[j])
  && (forall i, j | 0 <= i < n && 0 <= j < n && i < j :: !WouldIndulge(chairs[i], chairs[j]))
}

// --- Implementation ---

method KidsSeating(n: int) returns (chairs: seq<int>)
  requires n >= 0
  ensures ValidSeating(chairs, n)
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

  // ===== SPEC POSITIVE TESTS =====
  // ValidSeating called with correct outputs for small n

  // From test pairs: n=1, correct output [4]
  expect ValidSeating([4], 1), "spec positive 1";
  // From test pair 1: n=2, correct output [6, 8]
  expect ValidSeating([6, 8], 2), "spec positive 2";
  // From test pair 1: n=3, correct output [8, 10, 12]
  expect ValidSeating([8, 10, 12], 3), "spec positive 3";
  // From test pair 1: n=4, correct output [10, 12, 14, 16]
  expect ValidSeating([10, 12, 14, 16], 4), "spec positive 4";
  // From test pair 2: n=5, correct output [12, 14, 16, 18, 20]
  expect ValidSeating([12, 14, 16, 18, 20], 5), "spec positive 5";
  // Edge case: n=0, empty seating
  expect ValidSeating([], 0), "spec positive 6";

  // ===== SPEC NEGATIVE TESTS =====
  // ValidSeating called with wrong outputs — should be false

  // Neg 1: n=2, wrong [7, 8] (first elem 7 instead of 6; Gcd(7,8)=1 => WouldIndulge)
  expect !ValidSeating([7, 8], 2), "spec negative 1";
  // Neg 2: n=1, wrong [5] (5 > 4*1=4, out of range)
  expect !ValidSeating([5], 1), "spec negative 2";
  // Neg 3: n=1, wrong [5] (same pattern as neg 2)
  expect !ValidSeating([5], 1), "spec negative 3";
  // Neg 4 scaled down from n=100: n=3, wrong [9, 10, 12] (first +1; Gcd(9,10)=1)
  expect !ValidSeating([9, 10, 12], 3), "spec negative 4";
  // Neg 5: n=2, wrong [7, 8] (same as neg 1)
  expect !ValidSeating([7, 8], 2), "spec negative 5";
  // Neg 6: n=9, wrong [21, 22, 24, 26, 28, 30, 32, 34, 36] (first +1; Gcd(21,22)=1)
  expect !ValidSeating([21, 22, 24, 26, 28, 30, 32, 34, 36], 9), "spec negative 6";

  // ===== IMPLEMENTATION TESTS =====

  // Test 1: n=2, n=3, n=4
  result := KidsSeating(2);
  expect result == [6, 8], "impl test 1: n=2 failed";

  result := KidsSeating(3);
  expect result == [8, 10, 12], "impl test 1: n=3 failed";

  result := KidsSeating(4);
  expect result == [10, 12, 14, 16], "impl test 1: n=4 failed";

  // Test 2: n=1 through 100
  var i := 1;
  while i <= 100
  {
    result := KidsSeating(i);
    expected := ExpectedChairs(i);
    expect result == expected, "impl test 2 failed";
    i := i + 1;
  }

  // Test 3: 100 times n=1, all output [4]
  i := 0;
  while i < 100
  {
    result := KidsSeating(1);
    expect result == [4], "impl test 3 failed";
    i := i + 1;
  }

  // Test 4: 100 times n=100
  expected := ExpectedChairs(100);
  i := 0;
  while i < 100
  {
    result := KidsSeating(100);
    expect result == expected, "impl test 4 failed";
    i := i + 1;
  }

  // Test 5: alternating n=2 and n=1, 100 times
  i := 0;
  while i < 100
  {
    if i % 2 == 0 {
      result := KidsSeating(2);
      expect result == [6, 8], "impl test 5: n=2 failed";
    } else {
      result := KidsSeating(1);
      expect result == [4], "impl test 5: n=1 failed";
    }
    i := i + 1;
  }

  // Test 6: n values [9,3,9,4,5,4,7,6,7]
  result := KidsSeating(9);
  expect result == [20, 22, 24, 26, 28, 30, 32, 34, 36], "impl test 6: n=9 (1) failed";

  result := KidsSeating(3);
  expect result == [8, 10, 12], "impl test 6: n=3 failed";

  result := KidsSeating(9);
  expect result == [20, 22, 24, 26, 28, 30, 32, 34, 36], "impl test 6: n=9 (2) failed";

  result := KidsSeating(4);
  expect result == [10, 12, 14, 16], "impl test 6: n=4 (1) failed";

  result := KidsSeating(5);
  expect result == [12, 14, 16, 18, 20], "impl test 6: n=5 failed";

  result := KidsSeating(4);
  expect result == [10, 12, 14, 16], "impl test 6: n=4 (2) failed";

  result := KidsSeating(7);
  expect result == [16, 18, 20, 22, 24, 26, 28], "impl test 6: n=7 (1) failed";

  result := KidsSeating(6);
  expect result == [14, 16, 18, 20, 22, 24], "impl test 6: n=6 failed";

  result := KidsSeating(7);
  expect result == [16, 18, 20, 22, 24, 26, 28], "impl test 6: n=7 (2) failed";

  print "All tests passed\n";
}