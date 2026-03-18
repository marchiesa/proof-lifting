function SeqMin(a: seq<int>): int
  requires |a| > 0
  decreases |a|
{
  if |a| == 1 then a[0]
  else
    var rest := SeqMin(a[..|a|-1]);
    if a[|a|-1] < rest then a[|a|-1] else rest
}

function SeqMax(a: seq<int>): int
  requires |a| > 0
  decreases |a|
{
  if |a| == 1 then a[0]
  else
    var rest := SeqMax(a[..|a|-1]);
    if a[|a|-1] > rest then a[|a|-1] else rest
}

predicate ValidStoreConfig(a: seq<int>, startId: int, totalBefore: int)
{
  totalBefore >= |a| &&
  forall i | 0 <= i < |a| :: startId <= a[i] < startId + totalBefore
}

predicate FeasibleStolenCount(a: seq<int>, k: int)
  requires |a| > 0
{
  k >= 0 &&
  exists x | SeqMax(a) - |a| - k + 1 <= x <= SeqMin(a) ::
    ValidStoreConfig(a, x, |a| + k)
}

predicate MinStolenCount(a: seq<int>, k: int)
  requires |a| > 0
{
  FeasibleStolenCount(a, k) &&
  (k == 0 || !FeasibleStolenCount(a, k - 1))
}

method Heist(a: seq<int>) returns (stolen: int)
  ensures |a| == 0 ==> stolen == 0
  ensures |a| > 0 ==> MinStolenCount(a, stolen)
{
  if |a| == 0 {
    return 0;
  }
  var lo := a[0];
  var hi := a[0];
  var i := 1;
  while i < |a|
  {
    if a[i] < lo {
      lo := a[i];
    }
    if a[i] > hi {
      hi := a[i];
    }
    i := i + 1;
  }
  var res := hi - lo + 1 - |a|;
  if res < 0 {
    return 0;
  }
  return res;
}

method Main()
{
  // ── Spec Positive Tests (small inputs, MinStolenCount with correct k) ──
  // Mapped from positive test pairs to small equivalents (len 1-3, values 0-5)
  // Test 1: [10,13,12,8]->2  ~  [0,3]->2
  expect MinStolenCount([0, 3], 2), "spec positive 1";
  // Test 2: [7,5,6,4,8]->0  ~  [0,1,2]->0
  expect MinStolenCount([0, 1, 2], 0), "spec positive 2";
  // Test 3: [2]->0  ~  [1]->0
  expect MinStolenCount([1], 0), "spec positive 3";
  // Test 4: large gap  ~  [0,5]->4
  expect MinStolenCount([0, 5], 4), "spec positive 4";
  // Test 8: [10,1]->8  ~  [0,4]->3
  expect MinStolenCount([0, 4], 3), "spec positive 5";
  // Test 10: [65,81,6]->73  ~  [0,2,4]->2
  expect MinStolenCount([0, 2, 4], 2), "spec positive 6";
  // Additional small cases
  expect MinStolenCount([2], 0), "spec positive 7";
  expect MinStolenCount([1, 3], 1), "spec positive 8";
  expect MinStolenCount([0, 1], 0), "spec positive 9";
  expect MinStolenCount([5], 0), "spec positive 10";

  // ── Spec Negative Tests (small inputs, MinStolenCount with wrong k = correct+1) ──
  // Mapped from negative test pairs (all have wrong = correct + 1)
  // Neg 1: [10,13,12,8] wrong=3  ~  [0,3] wrong=3
  expect !MinStolenCount([0, 3], 3), "spec negative 1";
  // Neg 2: [7,5,6,4,8] wrong=1  ~  [0,1,2] wrong=1
  expect !MinStolenCount([0, 1, 2], 1), "spec negative 2";
  // Neg 3: [2] wrong=1  ~  [1] wrong=1
  expect !MinStolenCount([1], 1), "spec negative 3";
  // Neg 4: large gap wrong  ~  [0,5] wrong=5
  expect !MinStolenCount([0, 5], 5), "spec negative 4";
  // Neg 8: [10,1] wrong=9  ~  [0,4] wrong=4
  expect !MinStolenCount([0, 4], 4), "spec negative 5";
  // Neg 10: [65,81,6] wrong=74  ~  [0,2,4] wrong=3
  expect !MinStolenCount([0, 2, 4], 3), "spec negative 6";
  // Additional small negative cases
  expect !MinStolenCount([2], 1), "spec negative 7";
  expect !MinStolenCount([1, 3], 2), "spec negative 8";
  expect !MinStolenCount([0, 1], 1), "spec negative 9";
  expect !MinStolenCount([5], 1), "spec negative 10";

  // ── Implementation Tests (full-size inputs) ──
  var r0 := Heist([]);
  expect r0 == 0, "impl test 0 failed";

  var r1 := Heist([10, 13, 12, 8]);
  expect r1 == 2, "impl test 1 failed";

  var r2 := Heist([7, 5, 6, 4, 8]);
  expect r2 == 0, "impl test 2 failed";

  var r3 := Heist([2]);
  expect r3 == 0, "impl test 3 failed";

  var r4 := Heist([1000000000, 500000000, 2]);
  expect r4 == 999999996, "impl test 4 failed";

  var r5 := Heist([793, 656, 534, 608, 971, 970, 670, 786, 978, 665, 92, 391, 328, 228, 340, 681, 495, 175, 659, 520, 179, 396, 554, 481, 631, 468, 799, 390, 563, 471]);
  expect r5 == 857, "impl test 5 failed";

  var r6 := Heist([194, 121, 110, 134, 172, 142, 195, 135, 186, 187, 128, 161, 185, 132, 117, 175, 178, 131, 143, 151, 170, 181, 188, 140, 133, 145, 119, 129, 179, 149, 109, 123, 124, 106, 100, 199, 197, 155, 141, 183]);
  expect r6 == 60, "impl test 6 failed";

  var r7 := Heist([96, 4, 9, 94, 31, 70, 45, 24, 67, 64, 77, 100, 89, 75, 38, 60, 8, 49, 28, 32]);
  expect r7 == 77, "impl test 7 failed";

  var r8 := Heist([10, 1]);
  expect r8 == 8, "impl test 8 failed";

  var r9 := Heist([796461544, 559476582]);
  expect r9 == 236984961, "impl test 9 failed";

  var r10 := Heist([65, 81, 6]);
  expect r10 == 73, "impl test 10 failed";

  var r11 := Heist([2830, 6117, 3663, 4414, 7223, 6665, 1779, 5891, 7065, 6591]);
  expect r11 == 5435, "impl test 11 failed";

  var r12 := Heist([1, 1000000000]);
  expect r12 == 999999998, "impl test 12 failed";

  var r13 := Heist([1000000000]);
  expect r13 == 0, "impl test 13 failed";

  var r14 := Heist([100000000]);
  expect r14 == 0, "impl test 14 failed";

  var r15 := Heist([10000000, 10000001, 10000002]);
  expect r15 == 0, "impl test 15 failed";

  var r16 := Heist([999999999, 1000000000]);
  expect r16 == 0, "impl test 16 failed";

  var r17 := Heist([999999998, 1000000000]);
  expect r17 == 1, "impl test 17 failed";

  var r18 := Heist([100000000, 100000001, 100000002]);
  expect r18 == 0, "impl test 18 failed";

  var r19 := Heist([1, 2, 4, 5, 6]);
  expect r19 == 1, "impl test 19 failed";

  var r20 := Heist([10000000, 100000000]);
  expect r20 == 89999999, "impl test 20 failed";

  print "All tests passed\n";
}