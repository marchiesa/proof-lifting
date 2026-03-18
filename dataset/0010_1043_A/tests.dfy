function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

predicate ValidK(a: seq<int>, k: int)
{
  forall i | 0 <= i < |a| :: k >= a[i]
}

predicate AwrukWins(a: seq<int>, k: int)
{
  k * |a| - Sum(a) > Sum(a)
}

predicate IsSmallestWinningK(a: seq<int>, k: int)
  requires |a| > 0
{
  ValidK(a, k) && AwrukWins(a, k) &&
  forall k' | 0 <= k' < k :: !(ValidK(a, k') && AwrukWins(a, k'))
}

method Elections(a: seq<int>) returns (k: int)
  requires |a| > 0
  requires forall i | 0 <= i < |a| :: a[i] >= 0
  ensures IsSmallestWinningK(a, k)
{
  var s := 0;
  var i := 0;
  while i < |a|
  {
    s := s + a[i];
    i := i + 1;
  }

  var m := a[0];
  i := 1;
  while i < |a|
  {
    if a[i] > m {
      m := a[i];
    }
    i := i + 1;
  }

  k := m;
  while k * |a| - s <= s
  {
    k := k + 1;
  }

  return;
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Small inputs where IsSmallestWinningK(input, correct_output) should be true
  expect IsSmallestWinningK([1], 3), "spec positive 1";           // [1] -> 3
  expect IsSmallestWinningK([0], 1), "spec positive 2";           // [0] -> 1
  expect IsSmallestWinningK([2], 5), "spec positive 3";           // [2] -> 5
  expect IsSmallestWinningK([1, 1], 3), "spec positive 4";        // [1,1] -> 3
  expect IsSmallestWinningK([0, 1], 2), "spec positive 5";        // [0,1] -> 2
  expect IsSmallestWinningK([1, 2], 4), "spec positive 6";        // [1,2] -> 4
  expect IsSmallestWinningK([2, 2], 5), "spec positive 7";        // [2,2] -> 5
  expect IsSmallestWinningK([1, 1, 1], 3), "spec positive 8";     // [1,1,1] -> 3
  expect IsSmallestWinningK([0, 0, 1], 1), "spec positive 9";     // [0,0,1] -> 1
  expect IsSmallestWinningK([1, 0], 2), "spec positive 10";       // [1,0] -> 2

  // ===== SPEC NEGATIVE TESTS =====
  // Small inputs where IsSmallestWinningK(input, wrong_output) should be false
  // Wrong values too large (correct + 1):
  expect !IsSmallestWinningK([1], 4), "spec negative 1";          // correct 3, wrong 4
  expect !IsSmallestWinningK([0], 2), "spec negative 2";          // correct 1, wrong 2
  expect !IsSmallestWinningK([2], 6), "spec negative 3";          // correct 5, wrong 6
  expect !IsSmallestWinningK([1, 1], 4), "spec negative 4";       // correct 3, wrong 4
  expect !IsSmallestWinningK([0, 1], 3), "spec negative 5";       // correct 2, wrong 3
  expect !IsSmallestWinningK([1, 2], 5), "spec negative 6";       // correct 4, wrong 5
  expect !IsSmallestWinningK([2, 2], 6), "spec negative 7";       // correct 5, wrong 6
  expect !IsSmallestWinningK([1, 1, 1], 4), "spec negative 8";    // correct 3, wrong 4
  // Wrong values too small (not winning):
  expect !IsSmallestWinningK([1], 2), "spec negative 9";          // correct 3, wrong 2
  expect !IsSmallestWinningK([2], 4), "spec negative 10";         // correct 5, wrong 4

  // ===== IMPLEMENTATION TESTS =====
  var r1 := Elections([1, 1, 1, 5, 1]);
  expect r1 == 5, "impl test 1 failed";

  var r2 := Elections([2, 2, 3, 2, 2]);
  expect r2 == 5, "impl test 2 failed";

  var r3 := Elections([100]);
  expect r3 == 201, "impl test 3 failed";

  var r4 := Elections([15, 5]);
  expect r4 == 21, "impl test 4 failed";

  var r5 := Elections([12, 5, 4, 3, 4, 4, 9, 2, 14, 13, 1, 6, 6, 6, 6, 3, 1, 14, 1, 10, 4, 9, 12, 3, 1, 6, 5, 6, 9, 14, 4, 1, 10, 5, 15, 8, 5, 11, 13, 2, 10, 11, 8, 12, 8, 15, 2, 8, 6, 3]);
  expect r5 == 15, "impl test 5 failed";

  var r6 := Elections([50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50]);
  expect r6 == 101, "impl test 6 failed";

  var r7 := Elections([100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100]);
  expect r7 == 201, "impl test 7 failed";

  var r8 := Elections([2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1]);
  expect r8 == 5, "impl test 8 failed";

  var r9 := Elections([26, 32, 47, 42, 13, 36, 42, 9, 16, 37, 9, 49, 42, 46, 47, 49, 26, 20, 37, 29, 38, 2, 3, 1, 22, 37, 13, 10, 9, 45, 28, 2, 41, 21, 36, 3, 4, 41, 13, 14, 39, 41, 7, 22, 21, 15, 21, 17, 17, 21, 34, 35, 4, 12, 49, 5, 12, 31, 37, 28, 37, 3, 24, 14, 42, 22, 50, 20, 27, 32, 10, 12, 19, 27, 8, 16, 29, 8, 40, 15, 42, 23, 49, 46, 31, 14, 9, 30, 100, 8, 48, 9, 44, 39, 25, 43, 50, 47, 31, 3]);
  expect r9 == 100, "impl test 9 failed";

  var r10 := Elections([1]);
  expect r10 == 3, "impl test 10 failed";

  var r11 := Elections([1, 1]);
  expect r11 == 3, "impl test 11 failed";

  var r12 := Elections([100, 100]);
  expect r12 == 201, "impl test 12 failed";

  var r13 := Elections([1, 2, 2, 2, 2, 2, 1, 2, 2, 1]);
  expect r13 == 4, "impl test 13 failed";

  var r14 := Elections([2, 2, 4, 4, 3, 1, 1, 2, 3, 2]);
  expect r14 == 5, "impl test 14 failed";

  var r15 := Elections([10, 20, 26, 13, 8, 23, 47, 47, 20, 49, 22, 6, 43, 7, 34, 1, 18, 48, 38, 7]);
  expect r15 == 49, "impl test 15 failed";

  var r16 := Elections([2, 2, 3, 3, 2, 3, 1, 2, 1, 3, 3, 2, 3, 3, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3]);
  expect r16 == 5, "impl test 16 failed";

  var r17 := Elections([3, 3, 5, 9, 9, 3, 2, 9, 10, 2, 3, 2, 3, 6, 5, 9, 10, 10, 6, 6, 2, 3, 9, 9, 9]);
  expect r17 == 12, "impl test 17 failed";

  var r18 := Elections([82, 51, 81, 14, 37, 17, 78, 92, 64, 15, 8, 86, 89, 8, 87, 77, 66, 10, 15, 12, 100, 25, 92, 47, 21, 78, 20, 63, 13, 49, 41, 36, 41, 79, 16, 87, 87, 69, 3, 76, 80, 60, 100, 49, 70, 59, 72, 8, 38, 71, 45, 97, 71, 14, 76, 54, 81, 4, 59, 46, 39, 29, 92, 3, 49, 22, 53, 99, 59, 52, 74, 31, 92, 43, 42, 23, 44, 9, 82, 47, 7, 40, 12, 9, 3, 55, 37, 85, 46, 22, 84, 52, 98, 41, 21, 77, 63, 17, 62, 91]);
  expect r18 == 102, "impl test 18 failed";

  var r19 := Elections([2, 2, 2, 2, 2, 2, 2, 2, 2, 2]);
  expect r19 == 5, "impl test 19 failed";

  var r20 := Elections([5, 5, 5, 5, 5, 5, 5, 5, 5, 5]);
  expect r20 == 11, "impl test 20 failed";

  print "All tests passed\n";
}