// --- Specification: predicates and functions modeling the problem ---

function Abs(x: int): int {
  if x >= 0 then x else -x
}

function Min(a: int, b: int): int {
  if a <= b then a else b
}

function TotalDistance(perm: seq<int>): int
  decreases |perm|
{
  if |perm| == 0 then 0
  else TotalDistance(perm[..|perm|-1]) + Abs(perm[|perm|-1] - |perm|)
}

predicate IsPermutation(perm: seq<int>, n: int) {
  |perm| == n &&
  (forall i | 0 <= i < n :: 1 <= perm[i] <= n) &&
  (forall i, j | 0 <= i < j < n :: perm[i] != perm[j])
}

predicate IsDerangement(perm: seq<int>, n: int) {
  |perm| == n &&
  (forall i | 0 <= i < n :: perm[i] != i + 1)
}

function RangeSet(lo: int, hi: int): set<int> {
  if lo > hi then {} else {lo} + RangeSet(lo + 1, hi)
}

function MinDistHelper(n: int, pos: int, remaining: set<int>, partialDist: int): int
  requires 0 <= pos <= n
  decreases n - pos, n + 1
{
  if pos == n then partialDist
  else MinDistScan(n, pos, remaining, partialDist, 1)
}

function MinDistScan(n: int, pos: int, remaining: set<int>, partialDist: int, v: int): int
  requires 0 <= pos < n
  requires 1 <= v
  decreases n - pos, n + 1 - v
{
  if v > n then
    n * n + 1
  else
    var rest := MinDistScan(n, pos, remaining, partialDist, v + 1);
    if v in remaining && v != pos + 1 then
      var branch := MinDistHelper(n, pos + 1, remaining - {v},
                                   partialDist + Abs(v - (pos + 1)));
      Min(branch, rest)
    else
      rest
}

function MinDerangementDistance(n: int): int
  requires n >= 2
{
  MinDistHelper(n, 0, RangeSet(1, n), 0)
}

// --- Methods ---

method PrettyPermutation(n: int) returns (perm: seq<int>)
  requires n >= 2
  ensures IsPermutation(perm, n)
  ensures IsDerangement(perm, n)
  ensures TotalDistance(perm) == MinDerangementDistance(n)
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
  // ================================================================
  // SPEC POSITIVE TESTS
  // Verify correct outputs satisfy all ensures predicates.
  // Small n only (2-5) so MinDerangementDistance brute-force is feasible.
  // ================================================================

  // Positive test pair 1 (n=2): perm=[2,1]
  expect IsPermutation([2,1], 2) && IsDerangement([2,1], 2) && TotalDistance([2,1]) == MinDerangementDistance(2), "spec positive 1a";
  // Positive test pair 1 (n=3): perm=[3,1,2]
  expect IsPermutation([3,1,2], 3) && IsDerangement([3,1,2], 3) && TotalDistance([3,1,2]) == MinDerangementDistance(3), "spec positive 1b";

  // Positive test pair 2 scaled down (n=2): perm=[2,1]
  expect IsPermutation([2,1], 2) && IsDerangement([2,1], 2) && TotalDistance([2,1]) == MinDerangementDistance(2), "spec positive 2a";
  // Positive test pair 2 scaled down (n=3): perm=[3,1,2]
  expect IsPermutation([3,1,2], 3) && IsDerangement([3,1,2], 3) && TotalDistance([3,1,2]) == MinDerangementDistance(3), "spec positive 2b";
  // Positive test pair 2 scaled down (n=4): perm=[2,1,4,3]
  expect IsPermutation([2,1,4,3], 4) && IsDerangement([2,1,4,3], 4) && TotalDistance([2,1,4,3]) == MinDerangementDistance(4), "spec positive 2c";
  // Positive test pair 2 scaled down (n=5): perm=[3,1,2,5,4]
  expect IsPermutation([3,1,2,5,4], 5) && IsDerangement([3,1,2,5,4], 5) && TotalDistance([3,1,2,5,4]) == MinDerangementDistance(5), "spec positive 2d";

  // Positive test pair 3 (n=2): perm=[2,1]
  expect IsPermutation([2,1], 2) && IsDerangement([2,1], 2) && TotalDistance([2,1]) == MinDerangementDistance(2), "spec positive 3";

  // Positive test pair 4 (n=3): perm=[3,1,2]
  expect IsPermutation([3,1,2], 3) && IsDerangement([3,1,2], 3) && TotalDistance([3,1,2]) == MinDerangementDistance(3), "spec positive 4";

  // Positive test pair 5 (n=4): perm=[2,1,4,3]
  expect IsPermutation([2,1,4,3], 4) && IsDerangement([2,1,4,3], 4) && TotalDistance([2,1,4,3]) == MinDerangementDistance(4), "spec positive 5";

  // Positive test pair 6 (n=5): perm=[3,1,2,5,4]
  expect IsPermutation([3,1,2,5,4], 5) && IsDerangement([3,1,2,5,4], 5) && TotalDistance([3,1,2,5,4]) == MinDerangementDistance(5), "spec positive 6";

  // Positive test pair 7 scaled down (n=2 sub-case of n=10 pattern): perm=[2,1]
  expect IsPermutation([2,1], 2) && IsDerangement([2,1], 2) && TotalDistance([2,1]) == MinDerangementDistance(2), "spec positive 7";

  // Positive test pair 8 scaled down (n=4 sub-case of n=50 pattern): perm=[2,1,4,3]
  expect IsPermutation([2,1,4,3], 4) && IsDerangement([2,1,4,3], 4) && TotalDistance([2,1,4,3]) == MinDerangementDistance(4), "spec positive 8";

  // Positive test pair 9 (n=2,3,4): all small
  expect IsPermutation([2,1], 2) && IsDerangement([2,1], 2) && TotalDistance([2,1]) == MinDerangementDistance(2), "spec positive 9a";
  expect IsPermutation([3,1,2], 3) && IsDerangement([3,1,2], 3) && TotalDistance([3,1,2]) == MinDerangementDistance(3), "spec positive 9b";
  expect IsPermutation([2,1,4,3], 4) && IsDerangement([2,1,4,3], 4) && TotalDistance([2,1,4,3]) == MinDerangementDistance(4), "spec positive 9c";

  // Positive test pair 10 (n=2,3,4,5): small sub-cases
  expect IsPermutation([2,1], 2) && IsDerangement([2,1], 2) && TotalDistance([2,1]) == MinDerangementDistance(2), "spec positive 10a";
  expect IsPermutation([3,1,2], 3) && IsDerangement([3,1,2], 3) && TotalDistance([3,1,2]) == MinDerangementDistance(3), "spec positive 10b";
  expect IsPermutation([2,1,4,3], 4) && IsDerangement([2,1,4,3], 4) && TotalDistance([2,1,4,3]) == MinDerangementDistance(4), "spec positive 10c";
  expect IsPermutation([3,1,2,5,4], 5) && IsDerangement([3,1,2,5,4], 5) && TotalDistance([3,1,2,5,4]) == MinDerangementDistance(5), "spec positive 10d";

  // ================================================================
  // SPEC NEGATIVE TESTS
  // Verify wrong outputs do NOT satisfy all ensures predicates.
  // Small n only; IsPermutation fails for all wrong outputs (short-circuits).
  // ================================================================

  // Negative test pair 1 (n=2, wrong=[3,1]): 3 out of range
  expect !(IsPermutation([3,1], 2) && IsDerangement([3,1], 2) && TotalDistance([3,1]) == MinDerangementDistance(2)), "spec negative 1";

  // Negative test pair 2 scaled down (n=2, wrong=[3,1]): first wrong sub-case
  expect !(IsPermutation([3,1], 2) && IsDerangement([3,1], 2) && TotalDistance([3,1]) == MinDerangementDistance(2)), "spec negative 2";

  // Negative test pair 3 (n=2, wrong=[3,1])
  expect !(IsPermutation([3,1], 2) && IsDerangement([3,1], 2) && TotalDistance([3,1]) == MinDerangementDistance(2)), "spec negative 3";

  // Negative test pair 4 (n=3, wrong=[4,1,2]): 4 out of range
  expect !(IsPermutation([4,1,2], 3) && IsDerangement([4,1,2], 3) && TotalDistance([4,1,2]) == MinDerangementDistance(3)), "spec negative 4";

  // Negative test pair 5 (n=4, wrong=[3,1,4,3]): duplicate 3
  expect !(IsPermutation([3,1,4,3], 4) && IsDerangement([3,1,4,3], 4) && TotalDistance([3,1,4,3]) == MinDerangementDistance(4)), "spec negative 5";

  // Negative test pair 6 (n=5, wrong=[4,1,2,5,4]): duplicate 4
  expect !(IsPermutation([4,1,2,5,4], 5) && IsDerangement([4,1,2,5,4], 5) && TotalDistance([4,1,2,5,4]) == MinDerangementDistance(5)), "spec negative 6";

  // Negative test pairs 7 (n=10) and 8 (n=50) skipped — too large for spec evaluation

  // Negative test pair 9 (n=2, wrong=[3,1])
  expect !(IsPermutation([3,1], 2) && IsDerangement([3,1], 2) && TotalDistance([3,1]) == MinDerangementDistance(2)), "spec negative 9";

  // Negative test pair 10 (n=2, wrong=[3,1])
  expect !(IsPermutation([3,1], 2) && IsDerangement([3,1], 2) && TotalDistance([3,1]) == MinDerangementDistance(2)), "spec negative 10";

  // ================================================================
  // IMPLEMENTATION TESTS
  // Call PrettyPermutation and check correct output for all test pairs.
  // ================================================================

  var r: seq<int>;

  // Test pair 1: n=2, n=3
  r := PrettyPermutation(2);
  expect r == [2, 1], "impl test 1a failed";
  r := PrettyPermutation(3);
  expect r == [3, 1, 2], "impl test 1b failed";

  // Test pair 3: n=2
  r := PrettyPermutation(2);
  expect r == [2, 1], "impl test 3 failed";

  // Test pair 4: n=3
  r := PrettyPermutation(3);
  expect r == [3, 1, 2], "impl test 4 failed";

  // Test pair 5: n=4
  r := PrettyPermutation(4);
  expect r == [2, 1, 4, 3], "impl test 5 failed";

  // Test pair 6: n=5
  r := PrettyPermutation(5);
  expect r == [3, 1, 2, 5, 4], "impl test 6 failed";

  // Test pair 7: n=10
  r := PrettyPermutation(10);
  expect r == [2, 1, 4, 3, 6, 5, 8, 7, 10, 9], "impl test 7 failed";

  // Test pair 8: n=50
  r := PrettyPermutation(50);
  expect r == [2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 12, 11, 14, 13, 16, 15, 18, 17, 20, 19, 22, 21, 24, 23, 26, 25, 28, 27, 30, 29, 32, 31, 34, 33, 36, 35, 38, 37, 40, 39, 42, 41, 44, 43, 46, 45, 48, 47, 50, 49], "impl test 8 failed";

  // Test pair 9: n=2,3,4
  r := PrettyPermutation(2);
  expect r == [2, 1], "impl test 9a failed";
  r := PrettyPermutation(3);
  expect r == [3, 1, 2], "impl test 9b failed";
  r := PrettyPermutation(4);
  expect r == [2, 1, 4, 3], "impl test 9c failed";

  // Test pair 10: n=2,3,4,5,6
  r := PrettyPermutation(2);
  expect r == [2, 1], "impl test 10a failed";
  r := PrettyPermutation(3);
  expect r == [3, 1, 2], "impl test 10b failed";
  r := PrettyPermutation(4);
  expect r == [2, 1, 4, 3], "impl test 10c failed";
  r := PrettyPermutation(5);
  expect r == [3, 1, 2, 5, 4], "impl test 10d failed";
  r := PrettyPermutation(6);
  expect r == [2, 1, 4, 3, 6, 5], "impl test 10e failed";

  // Test pair 2: comprehensive n=2..100
  var n := 2;
  while n <= 100 {
    r := PrettyPermutation(n);
    var expected := ComputeExpected(n);
    expect r == expected, "impl test 2 failed";
    n := n + 1;
  }

  print "All tests passed\n";
}