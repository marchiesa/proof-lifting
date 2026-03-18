// ===== Specification for Teams Forming =====

function Abs(x: int): int {
  if x >= 0 then x else -x
}

function SumSeq(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else SumSeq(s[..|s| - 1]) + s[|s| - 1]
}

predicate IsPermutation(p: seq<int>, n: int) {
  |p| == n &&
  (forall i | 0 <= i < n :: 0 <= p[i] < n) &&
  (forall i, j | 0 <= i < j < n :: p[i] != p[j])
}

predicate ValidTeamAssignment(a: seq<int>, d: seq<int>, p: seq<int>)
  requires |a| % 2 == 0
{
  var n := |a|;
  |d| == n && IsPermutation(p, n) &&
  (forall i | 0 <= i < n :: d[i] >= 0) &&
  (forall k | 0 <= k < n / 2 ::
    a[p[2 * k]] + d[p[2 * k]] == a[p[2 * k + 1]] + d[p[2 * k + 1]])
}

function AssignmentCost(d: seq<int>): int {
  SumSeq(d)
}

function InsertSorted(x: int, s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + InsertSorted(x, s[1..])
}

function SortSeq(a: seq<int>): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else InsertSorted(a[|a| - 1], SortSeq(a[..|a| - 1]))
}

function ConsecutivePairCost(s: seq<int>): int
  decreases |s|
{
  if |s| < 2 then 0
  else Abs(s[|s| - 1] - s[|s| - 2]) + ConsecutivePairCost(s[..|s| - 2])
}

function MinTeamCost(a: seq<int>): int {
  ConsecutivePairCost(SortSeq(a))
}

method TeamsForming(a: seq<int>) returns (ans: int)
  requires |a| % 2 == 0
  ensures ans >= 0
  ensures ans == MinTeamCost(a)
{
  var n := |a|;
  var arr := new int[n];
  var k := 0;
  while k < n {
    arr[k] := a[k];
    k := k + 1;
  }

  // Bubble sort
  var i := 0;
  while i < n {
    var j := 0;
    while j < n - 1 - i {
      if arr[j] > arr[j + 1] {
        var tmp := arr[j];
        arr[j] := arr[j + 1];
        arr[j + 1] := tmp;
      }
      j := j + 1;
    }
    i := i + 1;
  }

  // Sum differences of consecutive pairs
  ans := 0;
  i := 0;
  while i < n {
    ans := ans + arr[i + 1] - arr[i];
    i := i + 2;
  }
}

method Main()
{
  var result: int;

  // ===== SPEC POSITIVE TESTS =====
  // Testing: MinTeamCost(input) == correct_output (small inputs)

  // Scaled from Test 2: [1, 100] -> 99 => [1, 4] -> 3
  expect MinTeamCost([1, 4]) == 3, "spec positive 1";

  // Scaled from Test 12: [1, 1] -> 0 => [1, 1] -> 0
  expect MinTeamCost([1, 1]) == 0, "spec positive 2";

  // Scaled from Test 1: [5, 10, 2, 3, 14, 5] -> 5 => [2, 5, 1, 1, 5, 2] -> sort [1,1,2,2,5,5] -> 0+0+0 = 0
  // Better: [1, 3, 0, 2, 5, 4] -> sort [0,1,2,3,4,5] -> 1+1+1 = 3
  expect MinTeamCost([1, 3, 0, 2, 5, 4]) == 3, "spec positive 3";

  // Scaled from Test 4: all same => [3, 3, 3, 3] -> 0
  expect MinTeamCost([3, 3, 3, 3]) == 0, "spec positive 4";

  // Scaled from Test 5: two equal-count values => [1, 2, 2, 1] -> sort [1,1,2,2] -> 0+0 = 0
  expect MinTeamCost([1, 2, 2, 1]) == 0, "spec positive 5";

  // Scaled from Test 14: [3, 2, 99, 99] -> 1 => [2, 1, 5, 5] -> sort [1,2,5,5] -> 1+0 = 1
  expect MinTeamCost([2, 1, 5, 5]) == 1, "spec positive 6";

  // Scaled from Test 15: [1, 70] -> 69 => [0, 5] -> 5
  expect MinTeamCost([0, 5]) == 5, "spec positive 7";

  // Scaled from Test 8: mostly two values with one outlier => [3, 3, 1, 1, 1, 4] -> sort [1,1,1,3,3,4] -> 0+2+1 = 3
  expect MinTeamCost([3, 3, 1, 1, 1, 4]) == 3, "spec positive 8";

  // Empty sequence -> 0
  expect MinTeamCost([]) == 0, "spec positive 9";

  // [0, 0] -> 0
  expect MinTeamCost([0, 0]) == 0, "spec positive 10";

  // ===== SPEC NEGATIVE TESTS =====
  // Testing: MinTeamCost(input) != wrong_output (small inputs)

  // Scaled from Neg 1: wrong off by 1 => MinTeamCost([1, 4]) == 3, not 4
  expect MinTeamCost([1, 4]) != 4, "spec negative 1";

  // Scaled from Neg 2: wrong off by 1 => MinTeamCost([1, 4]) == 3, not 2 (wrong = correct+1 mapped)
  expect MinTeamCost([0, 5]) != 6, "spec negative 2";

  // Scaled from Neg 4: all same should be 0, not 1
  expect MinTeamCost([3, 3, 3, 3]) != 1, "spec negative 3";

  // Scaled from Neg 5: two equal-count values => 0, not 1
  expect MinTeamCost([1, 2, 2, 1]) != 1, "spec negative 4";

  // Scaled from Neg 6: paired values => 0, not 1
  expect MinTeamCost([1, 2, 1, 2]) != 1, "spec negative 5";

  // Scaled from Neg 3: off by 1 upward
  expect MinTeamCost([1, 3, 0, 2, 5, 4]) != 4, "spec negative 6";

  // Scaled from Neg 7: off by 1 upward
  expect MinTeamCost([2, 1, 5, 5]) != 2, "spec negative 7";

  // Scaled from Neg 8: off by 1 upward
  expect MinTeamCost([3, 3, 1, 1, 1, 4]) != 4, "spec negative 8";

  // Scaled from Neg 9: off by 1 upward
  expect MinTeamCost([1, 1]) != 1, "spec negative 9";

  // Scaled from Neg 10: wrong off by 1
  expect MinTeamCost([0, 0]) != 1, "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====
  // Testing: TeamsForming(input) returns correct output (full-size inputs)

  // Test 1
  result := TeamsForming([5, 10, 2, 3, 14, 5]);
  expect result == 5, "impl test 1 failed";

  // Test 2
  result := TeamsForming([1, 100]);
  expect result == 99, "impl test 2 failed";

  // Test 3
  result := TeamsForming([15, 14, 32, 65, 28, 96, 33, 93, 48, 28, 57, 20, 32, 20, 90, 42, 57, 53, 18, 58, 94, 21, 27, 29, 37, 22, 94, 45, 67, 60, 83, 23, 20, 23, 35, 93, 3, 42, 6, 46, 68, 46, 34, 25, 17, 16, 50, 5, 49, 91, 23, 76, 69, 100, 58, 68, 81, 32, 88, 41, 64, 29, 37, 13, 95, 25, 6, 59, 74, 58, 31, 35, 16, 80, 13, 80, 10, 59, 85, 18, 16, 70, 51, 40, 44, 28, 8, 76, 8, 87, 53, 86, 28, 100, 2, 73, 14, 100, 52, 9]);
  expect result == 60, "impl test 3 failed";

  // Test 4
  result := TeamsForming([25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25]);
  expect result == 0, "impl test 4 failed";

  // Test 5
  result := TeamsForming([45, 59, 59, 59, 45, 45, 45, 59, 45, 59, 45, 45, 59, 59, 45, 45, 45, 59, 45, 45, 45, 59, 45, 59, 59, 59, 45, 45, 45, 59, 45, 59, 59, 45, 45, 59, 59, 59, 59, 45, 59, 59, 45, 45, 45, 45, 59, 45, 59, 59, 59, 45, 45, 45, 59, 45, 45, 59, 59, 45, 45, 59, 45, 59, 59, 59, 59, 59, 59, 45, 45, 59, 45, 59, 59, 45, 45, 59, 59, 45, 59, 59, 45, 59, 59, 59, 45, 59, 45, 45, 59, 45, 59, 59, 45, 59, 59, 59, 59, 59]);
  expect result == 0, "impl test 5 failed";

  // Test 6
  result := TeamsForming([89, 51, 37, 17, 13, 97, 78, 26, 44, 82, 36, 75, 39, 76, 96, 34, 88, 69, 27, 28, 93, 31, 53, 14, 93, 78, 71, 95, 44, 12, 34, 96, 97, 88, 37, 36, 16, 78, 13, 87, 41, 27, 44, 38, 17, 72, 93, 31, 27, 51, 12, 53, 12, 23, 14, 9, 39, 87, 76, 97, 28, 39, 27, 81, 93, 15, 1, 71, 78, 26, 75, 82, 89, 39, 9, 81, 53, 1, 26, 26, 12, 38, 38, 72, 99, 44, 1, 1, 16, 23, 27, 53, 15, 97, 41, 38, 27, 95, 99, 69]);
  expect result == 0, "impl test 6 failed";

  // Test 7
  result := TeamsForming([98, 52, 63, 2, 18, 96, 31, 58, 84, 40, 41, 45, 66, 100, 46, 71, 26, 48, 81, 20, 73, 91, 68, 76, 13, 93, 17, 29, 64, 95, 79, 21, 55, 75, 19, 85, 54, 51, 89, 78, 15, 87, 43, 59, 36, 1, 90, 35, 65, 56, 62, 28, 86, 5, 82, 49, 3, 99, 33, 9, 92, 32, 74, 69, 27, 22, 77, 16, 44, 94, 34, 6, 57, 70, 23, 12, 61, 25, 8, 11, 67, 47, 83, 88, 10, 14, 30, 7, 97, 60, 42, 37, 24, 38, 53, 50, 4, 80, 72, 39]);
  expect result == 50, "impl test 7 failed";

  // Test 8
  result := TeamsForming([32, 32, 32, 3, 32, 3, 32, 32, 3, 32, 32, 3, 32, 3, 32, 32, 32, 32, 32, 32, 3, 3, 3, 3, 3, 32, 32, 3, 32, 3, 32, 3, 32, 32, 32, 32, 32, 3, 3, 3, 3, 3, 3, 32, 3, 3, 3, 3, 32, 32, 32, 32, 32, 3, 3, 3, 3, 32, 32, 32, 32, 32, 3, 32, 32, 32, 3, 3, 32, 32, 32, 3, 3, 32, 32, 32, 3, 3, 33, 32, 3, 32, 3, 32, 32, 3, 3, 3, 32, 3, 3, 32, 32, 32, 32, 32, 32, 32, 3, 32]);
  expect result == 1, "impl test 8 failed";

  // Test 9
  result := TeamsForming([31, 76, 76, 31, 31, 31, 31, 31, 31, 76, 31, 31, 76, 31, 31, 76, 31, 76, 31, 76, 31, 76, 76, 31, 31, 76, 76, 76, 31, 31, 31, 31, 31, 76, 31, 76, 31, 31, 31, 76, 76, 76, 76, 31, 76, 76, 31, 76, 76, 31, 76, 31, 31, 76, 31, 76, 31, 76, 31, 31, 76, 31, 31, 31, 31, 31, 76, 31, 31, 31, 31, 76, 31, 31, 31, 76, 76, 31, 31, 31, 76, 31, 76, 31, 76, 32, 77, 76, 76, 31, 76, 31, 31, 31, 76, 31, 31, 31, 76, 31]);
  expect result == 2, "impl test 9 failed";

  // Test 10
  result := TeamsForming([1, 1, 100, 100, 1, 100, 1, 1, 1, 1, 1, 1, 100, 1, 100, 100, 100, 1, 1, 100, 100, 100, 100, 100, 1, 100, 1, 100, 1, 1, 1, 100, 1, 1, 100, 1, 100, 1, 1, 1, 100, 100, 1, 1, 1, 100, 100, 100, 100, 100, 1, 100, 100, 1, 1, 1, 1, 100, 1, 1, 100, 1, 1, 1, 1, 100, 100, 100, 1, 100, 1, 100, 100, 100, 1, 1, 100, 100, 100, 100, 1, 100, 1, 100, 100, 1, 100, 1, 100, 100, 100, 100, 100, 100, 1, 1, 1, 100, 100, 1]);
  expect result == 99, "impl test 10 failed";

  // Test 11
  result := TeamsForming([55, 2, 69, 13, 65, 71, 65, 8, 9, 87, 57, 43, 64, 53, 3, 74, 55, 31, 87, 5, 79, 47, 9, 29, 5, 31, 59, 1, 79, 97, 48, 91, 36, 40, 92, 37, 76, 73, 21, 44, 98, 55, 47, 1, 96, 63, 37, 83, 35, 8, 50, 54, 84, 100, 62, 98, 88, 1, 78, 57, 48, 46, 55, 49, 30, 100, 11, 39, 27, 61, 38, 55, 67, 16, 95, 25, 76, 67, 20, 46, 91, 91, 50, 33, 65, 64, 82, 30, 31, 42, 85, 78, 42, 29, 2, 69, 12, 50, 54, 79]);
  expect result == 47, "impl test 11 failed";

  // Test 12
  result := TeamsForming([1, 1]);
  expect result == 0, "impl test 12 failed";

  // Test 13
  result := TeamsForming([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]);
  expect result == 0, "impl test 13 failed";

  // Test 14
  result := TeamsForming([3, 2, 99, 99]);
  expect result == 1, "impl test 14 failed";

  // Test 15
  result := TeamsForming([1, 70]);
  expect result == 69, "impl test 15 failed";

  // Test 16
  result := TeamsForming([1, 71]);
  expect result == 70, "impl test 16 failed";

  print "All tests passed\n";
}