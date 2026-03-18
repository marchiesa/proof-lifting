function SeqMax(s: seq<int>): int
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0]
  else
    var m := SeqMax(s[..|s| - 1]);
    if s[|s| - 1] > m then s[|s| - 1] else m
}

function SeqMin(s: seq<int>): int
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0]
  else
    var m := SeqMin(s[..|s| - 1]);
    if s[|s| - 1] < m then s[|s| - 1] else m
}

function SwapAdj(s: seq<int>, i: int): seq<int>
  requires 0 <= i < |s| - 1
  ensures |SwapAdj(s, i)| == |s|
{
  s[i := s[i + 1]][i + 1 := s[i]]
}

predicate GeneralApproves(lineup: seq<int>, original: seq<int>)
  requires |lineup| > 0 && |original| > 0 && |lineup| == |original|
{
  lineup[0] == SeqMax(original) && lineup[|lineup| - 1] == SeqMin(original)
}

predicate CanReachApproved(s: seq<int>, original: seq<int>, budget: int)
  requires |s| > 0 && |original| > 0 && |s| == |original|
  requires budget >= 0
  decreases budget
{
  GeneralApproves(s, original)
  ||
  (budget > 0 &&
   exists i | 0 <= i < |s| - 1 :: CanReachApproved(SwapAdj(s, i), original, budget - 1))
}

// Combined postcondition: swaps is the minimum budget to reach an approved lineup
predicate IsMinBudget(a: seq<int>, swaps: int)
  requires |a| > 0
  requires swaps >= 0
{
  CanReachApproved(a, a, swaps) &&
  forall k | 0 <= k < swaps :: !CanReachApproved(a, a, k)
}

method ArrivalOfTheGeneral(a: seq<int>) returns (swaps: int)
  ensures |a| == 0 ==> swaps == 0
  ensures |a| > 0 ==> swaps >= 0 && CanReachApproved(a, a, swaps)
  ensures |a| > 0 ==> forall k | 0 <= k < swaps :: !CanReachApproved(a, a, k)
{
  var n := |a|;
  if n == 0 {
    return 0;
  }

  var mn := a[0];
  var mx := a[0];
  var i := 1;
  while i < n {
    if a[i] < mn { mn := a[i]; }
    if a[i] > mx { mx := a[i]; }
    i := i + 1;
  }

  var res := n * n;

  // Strategy 1: move max to front first, then min to end
  var cur := 0;
  var na := new int[n];
  i := 0;
  while i < n {
    na[i] := a[i];
    i := i + 1;
  }

  var pmx := -1;
  i := 0;
  while i < n {
    if na[i] == mx { pmx := i; break; }
    i := i + 1;
  }

  i := pmx - 1;
  while i >= 0 {
    var tmp := na[i]; na[i] := na[i + 1]; na[i + 1] := tmp;
    cur := cur + 1;
    i := i - 1;
  }

  var pmn := -1;
  i := n - 1;
  while i >= 0 {
    if na[i] == mn { pmn := i; break; }
    i := i - 1;
  }

  i := pmn;
  while i < n - 1 {
    var tmp := na[i]; na[i] := na[i + 1]; na[i + 1] := tmp;
    cur := cur + 1;
    i := i + 1;
  }

  if cur < res { res := cur; }

  // Strategy 2: move min to end first, then max to front
  cur := 0;
  i := 0;
  while i < n {
    na[i] := a[i];
    i := i + 1;
  }

  pmn := -1;
  i := n - 1;
  while i >= 0 {
    if na[i] == mn { pmn := i; break; }
    i := i - 1;
  }

  i := pmn;
  while i < n - 1 {
    var tmp := na[i]; na[i] := na[i + 1]; na[i + 1] := tmp;
    cur := cur + 1;
    i := i + 1;
  }

  pmx := -1;
  i := 0;
  while i < n {
    if na[i] == mx { pmx := i; break; }
    i := i + 1;
  }

  i := pmx - 1;
  while i >= 0 {
    var tmp := na[i]; na[i] := na[i + 1]; na[i + 1] := tmp;
    cur := cur + 1;
    i := i - 1;
  }

  if cur < res { res := cur; }

  swaps := res;
}

method Main()
{
  // ========== SPEC POSITIVE TESTS ==========
  // Small inputs (length 1-3, values 0-5) verifying the combined ensures predicate.
  // IsMinBudget(a, s) <==> CanReachApproved(a, a, s) && forall k < s :: !CanReachApproved(a, a, k)

  // [5] -> 0: single element, trivially approved
  expect IsMinBudget([5], 0), "spec positive 1";

  // [2, 1] -> 0: max=2 at front, min=1 at end, already approved
  expect IsMinBudget([2, 1], 0), "spec positive 2";

  // [1, 2] -> 1: one swap needed to get max to front and min to end
  expect IsMinBudget([1, 2], 1), "spec positive 3";

  // [1, 2, 1] -> 1: swap max(2) to front (same as Test 8)
  expect IsMinBudget([1, 2, 1], 1), "spec positive 4";

  // [3, 3, 1] -> 0: max=3 at front, min=1 at end, approved
  expect IsMinBudget([3, 3, 1], 0), "spec positive 5";

  // [1, 3, 2] -> 2: move max to front then min to end
  expect IsMinBudget([1, 3, 2], 2), "spec positive 6";

  // [1, 2, 3] -> 3: worst case for length 3
  expect IsMinBudget([1, 2, 3], 3), "spec positive 7";

  // ========== SPEC NEGATIVE TESTS ==========
  // Wrong (too-large) answers fail minimality: a smaller budget already works.

  // correct=1, wrong=2
  expect !IsMinBudget([1, 2], 2), "spec negative 1";

  // correct=0, wrong=1
  expect !IsMinBudget([2, 1], 1), "spec negative 2";

  // correct=0, wrong=1
  expect !IsMinBudget([3, 3, 1], 1), "spec negative 3";

  // correct=1, wrong=2
  expect !IsMinBudget([1, 2, 1], 2), "spec negative 4";

  // correct=2, wrong=3
  expect !IsMinBudget([1, 3, 2], 3), "spec negative 5";

  // correct=1, wrong=2
  expect !IsMinBudget([2, 3, 1], 2), "spec negative 6";

  // correct=3, wrong=4
  expect !IsMinBudget([1, 2, 3], 4), "spec negative 7";

  // ========== IMPLEMENTATION TESTS ==========
  var r1 := ArrivalOfTheGeneral([33, 44, 11, 22]);
  expect r1 == 2, "impl test 1 failed";

  var r2 := ArrivalOfTheGeneral([10, 10, 58, 31, 63, 40, 76]);
  expect r2 == 10, "impl test 2 failed";

  var r3 := ArrivalOfTheGeneral([88, 89]);
  expect r3 == 1, "impl test 3 failed";

  var r4 := ArrivalOfTheGeneral([100, 95, 100, 100, 88]);
  expect r4 == 0, "impl test 4 failed";

  var r5 := ArrivalOfTheGeneral([48, 48, 48, 48, 45, 45, 45]);
  expect r5 == 0, "impl test 5 failed";

  var r6 := ArrivalOfTheGeneral([68, 47, 67, 29, 63, 71, 71, 65, 54, 56]);
  expect r6 == 10, "impl test 6 failed";

  var r7 := ArrivalOfTheGeneral([77, 68, 96, 60, 92, 75, 61, 60, 66, 79, 80, 65, 60, 95, 92]);
  expect r7 == 4, "impl test 7 failed";

  var r8 := ArrivalOfTheGeneral([1, 2, 1]);
  expect r8 == 1, "impl test 8 failed";

  var r9 := ArrivalOfTheGeneral([30, 30, 30, 14, 30, 14, 30, 30, 30, 14, 30, 14, 14, 30, 14, 14, 30, 14, 14, 14]);
  expect r9 == 0, "impl test 9 failed";

  var r10 := ArrivalOfTheGeneral([37, 41, 46, 39, 47, 39, 44, 47, 44, 42, 44, 43, 47, 39, 46, 39, 38, 42, 39, 37, 40, 44, 41, 42, 41, 42, 39, 42, 36, 36, 42, 36, 42, 42, 42]);
  expect r10 == 7, "impl test 10 failed";

  var r11 := ArrivalOfTheGeneral([99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 98, 99, 99, 99, 99, 99, 99, 99, 99, 100, 99, 99, 99, 99, 99, 99]);
  expect r11 == 47, "impl test 11 failed";

  var r12 := ArrivalOfTheGeneral([48, 52, 44, 54, 53, 56, 62, 49, 39, 41, 53, 39, 40, 64, 53, 50, 62, 48, 40, 52, 51, 48, 40, 52, 61, 62, 62, 61, 48, 64, 55, 57, 56, 40, 48, 58, 41, 60, 60, 56, 64, 50, 64, 45, 48, 45, 46, 63, 59, 57]);
  expect r12 == 50, "impl test 12 failed";

  var r13 := ArrivalOfTheGeneral([7, 24, 17, 19, 6, 19, 10, 11, 12, 22, 14, 5, 5, 11, 13, 10, 24, 19, 24, 24, 24, 11, 21, 20, 4, 14, 24, 24, 18, 13, 24, 3, 20, 3, 3, 3, 3, 9, 3, 9, 22, 22, 16, 3, 3, 3, 15, 11, 3, 3, 8, 17, 10, 13, 3, 14, 13]);
  expect r13 == 3, "impl test 13 failed";

  var r14 := ArrivalOfTheGeneral([58, 50, 35, 44, 35, 37, 36, 58, 38, 36, 58, 56, 56, 49, 48, 56, 58, 43, 40, 44, 52, 44, 58, 58, 57, 50, 43, 35, 55, 39, 38, 49, 53, 56, 50, 42, 41, 56, 34, 57, 49, 38, 34, 51, 56, 38, 58, 40, 53, 46, 48, 34, 38, 43, 49, 49, 58, 56, 41, 43, 44, 34, 38, 48, 36]);
  expect r14 == 3, "impl test 14 failed";

  var r15 := ArrivalOfTheGeneral([70, 48, 49, 48, 49, 71, 48, 53, 55, 69, 48, 53, 54, 58, 53, 63, 48, 48, 69, 67, 72, 75, 71, 75, 74, 74, 57, 63, 65, 60, 48, 48, 65, 48, 48, 51, 50, 49, 62, 53, 76, 68, 76, 56, 76, 76, 64, 76, 76, 57, 61, 76, 73, 51, 59, 76, 65, 50, 69, 50, 76, 67, 76, 63, 62, 74, 74, 58, 73]);
  expect r15 == 73, "impl test 15 failed";

  var r16 := ArrivalOfTheGeneral([70, 65, 64, 71, 71, 64, 71, 64, 68, 71, 65, 64, 65, 68, 71, 66, 66, 69, 68, 63, 69, 65, 71, 69, 68, 68, 71, 67, 71, 65, 65, 65, 71, 71, 65, 69, 63, 66, 62, 67, 64, 63, 62, 64, 67, 65, 62, 69, 62, 64, 69, 62, 67, 64, 67, 70, 64, 63, 64, 64, 69, 62, 62, 64, 70, 62, 62, 68, 67, 69, 62, 64, 66, 70, 68]);
  expect r16 == 7, "impl test 16 failed";

  var r17 := ArrivalOfTheGeneral([92, 95, 84, 85, 94, 80, 90, 86, 80, 92, 95, 84, 86, 83, 86, 83, 93, 91, 95, 92, 84, 88, 82, 84, 84, 84, 80, 94, 93, 80, 94, 80, 95, 83, 85, 80, 95, 95, 80, 84, 86, 92, 83, 81, 90, 87, 81, 89, 92, 93, 80, 87, 90, 85, 93, 85, 93, 94, 93, 89, 94, 83, 93, 91, 80, 83, 90, 94, 95, 80, 95, 92, 85, 84, 93, 94, 94, 82, 91, 95, 95, 89, 85, 94]);
  expect r17 == 15, "impl test 17 failed";

  var r18 := ArrivalOfTheGeneral([86, 87, 72, 77, 82, 71, 75, 78, 61, 67, 79, 90, 64, 94, 94, 74, 85, 87, 73, 76, 71, 71, 60, 69, 77, 73, 76, 80, 82, 57, 62, 57, 57, 83, 76, 72, 75, 87, 72, 94, 77, 85, 59, 82, 86, 69, 62, 80, 95, 73, 83, 94, 79, 85, 91, 68, 85, 74, 93, 95, 68, 75, 89, 93, 83, 78, 95, 78, 83, 77, 81, 85, 66, 92, 63, 65, 75, 78, 67, 91, 77, 74, 59, 86, 77, 76, 90, 67, 70, 64]);
  expect r18 == 104, "impl test 18 failed";

  var r19 := ArrivalOfTheGeneral([94, 98, 96, 94, 95, 98, 98, 95, 98, 94, 94, 98, 95, 95, 99, 97, 97, 94, 95, 98, 94, 98, 96, 98, 96, 98, 97, 95, 94, 94, 94, 97, 94, 96, 98, 98, 98, 94, 96, 95, 94, 95, 97, 97, 97, 98, 94, 98, 96, 95, 98, 96, 96, 98, 94, 97, 96, 98, 97, 95, 97, 98, 94, 95, 94, 94, 97, 94, 96, 97, 97, 93, 94, 95, 95, 94, 96, 98, 97, 96, 94, 98, 98, 96, 96, 96, 96, 96, 94, 96, 97]);
  expect r19 == 33, "impl test 19 failed";

  var r20 := ArrivalOfTheGeneral([44, 28, 32, 29, 41, 41, 36, 39, 40, 39, 41, 35, 41, 28, 35, 27, 41, 34, 28, 38, 43, 43, 41, 38, 27, 26, 28, 36, 30, 29, 39, 32, 35, 35, 32, 30, 39, 30, 37, 27, 41, 41, 28, 30, 43, 31, 35, 33, 36, 28, 44, 40, 41, 35, 31, 42, 37, 38, 37, 34, 39, 40, 27, 40, 33, 33, 44, 43, 34, 33, 34, 34, 35, 38, 38, 37, 30, 39, 35, 41, 45, 42, 41, 32, 33, 33, 31, 30, 43, 41, 43, 43]);
  expect r20 == 145, "impl test 20 failed";

  print "All tests passed\n";
}