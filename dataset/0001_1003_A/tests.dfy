// --- Formal Specification ---

function Count(a: seq<int>, v: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[|a|-1] == v then 1 else 0) + Count(a[..|a|-1], v)
}

predicate IsValidAssignment(a: seq<int>, assign: seq<int>, p: int)
{
  |assign| == |a| &&
  (forall i | 0 <= i < |a| :: 0 <= assign[i] < p) &&
  (forall i, j | 0 <= i < |a| && 0 <= j < |a| && i < j ::
    a[i] == a[j] ==> assign[i] != assign[j])
}

function BuildAssignment(a: seq<int>, p: int): seq<int>
  requires p > 0
  decreases |a|
{
  if |a| == 0 then []
  else BuildAssignment(a[..|a|-1], p) + [Count(a[..|a|-1], a[|a|-1]) % p]
}

predicate CanDistribute(a: seq<int>, p: int)
{
  if p <= 0 then |a| == 0
  else IsValidAssignment(a, BuildAssignment(a, p), p)
}

predicate IsMinPockets(a: seq<int>, p: int)
{
  CanDistribute(a, p) &&
  (p == 0 || !CanDistribute(a, p - 1))
}

// --- Implementation ---

method PolycarpsPockets(a: seq<int>) returns (pockets: int)
  ensures IsMinPockets(a, pockets)
{
  var dic: map<int, int> := map[];
  var i := 0;
  while i < |a|
  {
    var num := a[i];
    if num in dic {
      dic := dic[num := dic[num] + 1];
    } else {
      dic := dic[num := 1];
    }
    i := i + 1;
  }

  var maxCount := 0;
  var keys := a;
  var j := 0;
  while j < |keys|
  {
    var num := keys[j];
    if num in dic && dic[num] > maxCount {
      maxCount := dic[num];
    }
    j := j + 1;
  }
  pockets := maxCount;
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // Small inputs testing IsMinPockets directly

  // From Test 2 scaled: single element -> 1
  expect IsMinPockets([1], 1), "spec positive 1";

  // From Test 1 scaled: [1,2,2] max freq 2 -> 2
  expect IsMinPockets([1, 2, 2], 2), "spec positive 2";

  // From Test 6 scaled: all distinct -> 1
  expect IsMinPockets([1, 2, 3], 1), "spec positive 3";

  // From Test 16 (already small): [2,1,1] -> 2
  expect IsMinPockets([2, 1, 1], 2), "spec positive 4";

  // From Test 3/4 scaled: all same x3 -> 3
  expect IsMinPockets([1, 1, 1], 3), "spec positive 5";

  // Edge case: empty -> 0
  expect IsMinPockets([], 0), "spec positive 6";

  // From Test 7 scaled: pair -> 2
  expect IsMinPockets([1, 1], 2), "spec positive 7";

  // === SPEC NEGATIVE TESTS ===
  // Small inputs testing IsMinPockets rejects wrong answers

  // From Neg 2 scaled: [1] wrong 2 (too high)
  expect !IsMinPockets([1], 2), "spec negative 1";

  // From Neg 1 scaled: [1,2,2] wrong 3 (too high)
  expect !IsMinPockets([1, 2, 2], 3), "spec negative 2";

  // From Neg 6 scaled: [1,2,3] wrong 2 (too high)
  expect !IsMinPockets([1, 2, 3], 2), "spec negative 3";

  // From Neg 3/4 scaled: [1,1,1] wrong 4 (too high)
  expect !IsMinPockets([1, 1, 1], 4), "spec negative 4";

  // From Neg 9 scaled: [1,1] wrong 1 (too low)
  expect !IsMinPockets([1, 1], 1), "spec negative 5";

  // From Neg 7 scaled: [2,1,1] wrong 3 (too high)
  expect !IsMinPockets([2, 1, 1], 3), "spec negative 6";

  // From Neg 8 scaled: [1,1] wrong 3 (too high)
  expect !IsMinPockets([1, 1], 3), "spec negative 7";

  // === IMPLEMENTATION TESTS ===

  // Test 1
  var r1 := PolycarpsPockets([1, 2, 4, 3, 3, 2]);
  expect r1 == 2, "impl test 1 failed";

  // Test 2
  var r2 := PolycarpsPockets([100]);
  expect r2 == 1, "impl test 2 failed";

  // Test 3
  var r3 := PolycarpsPockets([100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100]);
  expect r3 == 100, "impl test 3 failed";

  // Test 4
  var r4 := PolycarpsPockets([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]);
  expect r4 == 100, "impl test 4 failed";

  // Test 5
  var r5 := PolycarpsPockets([59, 47, 39, 47, 47, 71, 47, 28, 58, 47, 35, 79, 58, 47, 38, 47, 47, 47, 47, 27, 47, 43, 29, 95, 47, 49, 46, 71, 47, 74, 79, 47, 47, 32, 45, 67, 47, 47, 30, 37, 47, 47, 16, 67, 22, 76, 47, 86, 84, 10, 5, 47, 47, 47, 47, 47, 1, 51, 47, 54, 47, 8, 47, 47, 9, 47, 47, 47, 47, 28, 47, 47, 26, 47, 47, 47, 47, 47, 47, 92, 47, 47, 77, 47, 47, 24, 45, 47, 10, 47, 47, 89, 47, 27, 47, 89, 47, 67, 24, 71]);
  expect r5 == 51, "impl test 5 failed";

  // Test 6
  var r6 := PolycarpsPockets([45, 99, 10, 27, 16, 85, 39, 38, 17, 32, 15, 23, 67, 48, 50, 97, 42, 70, 62, 30, 44, 81, 64, 73, 34, 22, 46, 5, 83, 52, 58, 60, 33, 74, 47, 88, 18, 61, 78, 53, 25, 95, 94, 31, 3, 75, 1, 57, 20, 54, 59, 9, 68, 7, 77, 43, 21, 87, 86, 24, 4, 80, 11, 49, 2, 72, 36, 84, 71, 8, 65, 55, 79, 100, 41, 14, 35, 89, 66, 69, 93, 37, 56, 82, 90, 91, 51, 19, 26, 92, 6, 96, 13, 98, 12, 28, 76, 40, 63, 29]);
  expect r6 == 1, "impl test 6 failed";

  // Test 7
  var r7 := PolycarpsPockets([45, 29, 5, 2, 6, 50, 22, 36, 14, 15, 9, 48, 46, 20, 8, 37, 7, 47, 12, 50, 21, 38, 18, 27, 33, 19, 40, 10, 5, 49, 38, 42, 34, 37, 27, 30, 35, 24, 10, 3, 40, 49, 41, 3, 4, 44, 13, 25, 28, 31, 46, 36, 23, 1, 1, 23, 7, 22, 35, 26, 21, 16, 48, 42, 32, 8, 11, 16, 34, 11, 39, 32, 47, 28, 43, 41, 39, 4, 14, 19, 26, 45, 13, 18, 15, 25, 2, 44, 17, 29, 17, 33, 43, 6, 12, 30, 9, 20, 31, 24]);
  expect r7 == 2, "impl test 7 failed";

  // Test 8
  var r8 := PolycarpsPockets([7, 7, 3, 3, 7, 4, 5, 6, 4, 3, 7, 5, 6, 4, 5, 4, 4, 5, 6, 7, 7, 7, 4, 5, 5, 5, 3, 7, 6, 3, 4, 6, 3, 6, 4, 4, 5, 4, 6, 6, 3, 5, 6, 3, 5, 3, 3, 7, 7, 6]);
  expect r8 == 10, "impl test 8 failed";

  // Test 9
  var r9 := PolycarpsPockets([100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 99, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100]);
  expect r9 == 99, "impl test 9 failed";

  // Test 10
  var r10 := PolycarpsPockets([1, 2, 3, 3, 3, 1, 2]);
  expect r10 == 3, "impl test 10 failed";

  // Test 11
  var r11 := PolycarpsPockets([1, 2, 3, 4, 5]);
  expect r11 == 1, "impl test 11 failed";

  // Test 12
  var r12 := PolycarpsPockets([1, 2, 3, 4, 5, 6, 7]);
  expect r12 == 1, "impl test 12 failed";

  // Test 13
  var r13 := PolycarpsPockets([1, 2, 3, 4, 5, 6, 7, 8]);
  expect r13 == 1, "impl test 13 failed";

  // Test 14
  var r14 := PolycarpsPockets([1, 2, 3, 4, 5, 6, 7, 8, 9]);
  expect r14 == 1, "impl test 14 failed";

  // Test 15
  var r15 := PolycarpsPockets([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
  expect r15 == 1, "impl test 15 failed";

  // Test 16
  var r16 := PolycarpsPockets([2, 1, 1]);
  expect r16 == 2, "impl test 16 failed";

  // Test 17
  var r17 := PolycarpsPockets([1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 1]);
  expect r17 == 3, "impl test 17 failed";

  // Test 18
  var r18 := PolycarpsPockets([1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]);
  expect r18 == 11, "impl test 18 failed";

  // Test 19
  var r19 := PolycarpsPockets([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]);
  expect r19 == 13, "impl test 19 failed";

  // Test 20
  var r20 := PolycarpsPockets([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]);
  expect r20 == 14, "impl test 20 failed";

  print "All tests passed\n";
}