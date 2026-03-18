// ---- FORMAL SPECIFICATION ----

predicate TrainsCollide(b: int, l: int) {
  exists T | 0 <= T <= 101 :: b == T && l == T
}

predicate AllDistinct(s: seq<int>) {
  forall i | 0 <= i < |s| ::
    forall j | i + 1 <= j < |s| ::
      s[i] != s[j]
}

function CollisionPairsForOne(bi: int, bval: int, left: seq<int>): seq<(int, int)>
  decreases |left|
{
  if |left| == 0 then []
  else
    CollisionPairsForOne(bi, bval, left[..|left| - 1]) +
    (if TrainsCollide(bval, left[|left| - 1]) then [(bi, |left| - 1)] else [])
}

function CollisionPairs(bottom: seq<int>, left: seq<int>): seq<(int, int)>
  decreases |bottom|
{
  if |bottom| == 0 then []
  else
    CollisionPairs(bottom[..|bottom| - 1], left) +
    CollisionPairsForOne(|bottom| - 1, bottom[|bottom| - 1], left)
}

function MinHittingSet(pairs: seq<(int, int)>, cancelledB: set<int>, cancelledL: set<int>): int
  decreases |pairs|
{
  if |pairs| == 0 then |cancelledB| + |cancelledL|
  else
    var pair := pairs[|pairs| - 1];
    var rest := pairs[..|pairs| - 1];
    if pair.0 in cancelledB || pair.1 in cancelledL then
      MinHittingSet(rest, cancelledB, cancelledL)
    else
      var optB := MinHittingSet(rest, cancelledB + {pair.0}, cancelledL);
      var optL := MinHittingSet(rest, cancelledB, cancelledL + {pair.1});
      if optB <= optL then optB else optL
}

function MinCancellations(bottom: seq<int>, left: seq<int>): int {
  MinHittingSet(CollisionPairs(bottom, left), {}, {})
}

// ---- IMPLEMENTATION ----

method CancelTheTrains(bottom: seq<int>, left: seq<int>) returns (cancelled: int)
  requires forall i | 0 <= i < |bottom| :: 1 <= bottom[i] <= 100
  requires forall i | 0 <= i < |left| :: 1 <= left[i] <= 100
  requires AllDistinct(bottom)
  requires AllDistinct(left)
  ensures cancelled == MinCancellations(bottom, left)
{
  cancelled := 0;
  var h: map<int, int> := map[];

  var i := 0;
  while i < |bottom|
  {
    var x := bottom[i];
    if x in h {
      h := h[x := h[x] + 1];
    } else {
      h := h[x := 1];
    }
    i := i + 1;
  }

  var j := 0;
  while j < |left|
  {
    var x := left[j];
    if x in h && h[x] == 1 {
      cancelled := cancelled + 1;
    }
    j := j + 1;
  }
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Testing: MinCancellations(bottom, left) == expected

  // Test 1.1: bottom=[1], left=[3,4] → 0
  expect MinCancellations([1], [3, 4]) == 0, "spec positive 1.1";

  // Test 1.2: bottom=[1,3,4], left=[2,4] → 1
  expect MinCancellations([1, 3, 4], [2, 4]) == 1, "spec positive 1.2";

  // Test 1.3: skipped (9x14 inputs too large for bounded quantifier enumeration)

  // Test 2: bottom=[1], left=[1] → 1
  expect MinCancellations([1], [1]) == 1, "spec positive 2";

  // Test 3: bottom=[1,4], left=[2,3,5] → 0
  expect MinCancellations([1, 4], [2, 3, 5]) == 0, "spec positive 3";

  // Test 4: bottom=[1,2,3], left=[1,2,3] → 3
  expect MinCancellations([1, 2, 3], [1, 2, 3]) == 3, "spec positive 4";

  // Test 5: bottom=[1,2,3,4,5], left=[1,2,3,4,5] → 5
  expect MinCancellations([1, 2, 3, 4, 5], [1, 2, 3, 4, 5]) == 5, "spec positive 5";

  // Test 6: bottom=[3], left=[1,2,3,4,5] → 1
  expect MinCancellations([3], [1, 2, 3, 4, 5]) == 1, "spec positive 6";

  // Test 7: bottom=[2,5,7,8], left=[6] → 0
  expect MinCancellations([2, 5, 7, 8], [6]) == 0, "spec positive 7";

  // Test 8.1: bottom=[3,7], left=[3,7] → 2
  expect MinCancellations([3, 7], [3, 7]) == 2, "spec positive 8.1";

  // Test 8.2: bottom=[5], left=[5] → 1
  expect MinCancellations([5], [5]) == 1, "spec positive 8.2";

  // Test 9: bottom=[10,20,30], left=[5,10,20,40] → 2
  expect MinCancellations([10, 20, 30], [5, 10, 20, 40]) == 2, "spec positive 9";

  // Test 10.1: bottom=[1], left=[1] → 1
  expect MinCancellations([1], [1]) == 1, "spec positive 10.1";

  // Test 10.2: bottom=[1,2], left=[1,2] → 2
  expect MinCancellations([1, 2], [1, 2]) == 2, "spec positive 10.2";

  // Test 10.3: bottom=[1,2,3], left=[4,5,6] → 0
  expect MinCancellations([1, 2, 3], [4, 5, 6]) == 0, "spec positive 10.3";

  // Test 11: bottom=[2,4,8,15,23,50], left=[1,4,9,15,30,42,50] → 3
  expect MinCancellations([2, 4, 8, 15, 23, 50], [1, 4, 9, 15, 30, 42, 50]) == 3, "spec positive 11";

  // ===== SPEC NEGATIVE TESTS =====
  // Testing: MinCancellations(bottom, left) != wrong_output

  // Neg 1: bottom=[1], left=[3,4], wrong=1 (correct=0)
  expect MinCancellations([1], [3, 4]) != 1, "spec negative 1";

  // Neg 2: bottom=[1], left=[1], wrong=2 (correct=1)
  expect MinCancellations([1], [1]) != 2, "spec negative 2";

  // Neg 3: bottom=[1,4], left=[2,3,5], wrong=1 (correct=0)
  expect MinCancellations([1, 4], [2, 3, 5]) != 1, "spec negative 3";

  // Neg 4: bottom=[1,2,3], left=[1,2,3], wrong=4 (correct=3)
  expect MinCancellations([1, 2, 3], [1, 2, 3]) != 4, "spec negative 4";

  // Neg 5: bottom=[1,2,3,4,5], left=[1,2,3,4,5], wrong=6 (correct=5)
  expect MinCancellations([1, 2, 3, 4, 5], [1, 2, 3, 4, 5]) != 6, "spec negative 5";

  // Neg 6: bottom=[3], left=[1,2,3,4,5], wrong=2 (correct=1)
  expect MinCancellations([3], [1, 2, 3, 4, 5]) != 2, "spec negative 6";

  // Neg 7: bottom=[2,5,7,8], left=[6], wrong=1 (correct=0)
  expect MinCancellations([2, 5, 7, 8], [6]) != 1, "spec negative 7";

  // Neg 8: bottom=[3,7], left=[3,7], wrong=3 (correct=2)
  expect MinCancellations([3, 7], [3, 7]) != 3, "spec negative 8";

  // Neg 9: bottom=[10,20,30], left=[5,10,20,40], wrong=3 (correct=2)
  expect MinCancellations([10, 20, 30], [5, 10, 20, 40]) != 3, "spec negative 9";

  // Neg 10: bottom=[1], left=[1], wrong=2 (correct=1)
  expect MinCancellations([1], [1]) != 2, "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====
  var cancelled: int;

  // Test 1.1: bottom=[1], left=[3,4] → 0
  cancelled := CancelTheTrains([1], [3, 4]);
  expect cancelled == 0, "impl test 1.1 failed";

  // Test 1.2: bottom=[1,3,4], left=[2,4] → 1
  cancelled := CancelTheTrains([1, 3, 4], [2, 4]);
  expect cancelled == 1, "impl test 1.2 failed";

  // Test 1.3: bottom=[2,7,16,28,33,57,59,86,99], left=[3,9,14,19,25,26,28,35,41,59,85,87,99,100] → 3
  cancelled := CancelTheTrains([2, 7, 16, 28, 33, 57, 59, 86, 99], [3, 9, 14, 19, 25, 26, 28, 35, 41, 59, 85, 87, 99, 100]);
  expect cancelled == 3, "impl test 1.3 failed";

  // Test 2: bottom=[1], left=[1] → 1
  cancelled := CancelTheTrains([1], [1]);
  expect cancelled == 1, "impl test 2 failed";

  // Test 3: bottom=[1,4], left=[2,3,5] → 0
  cancelled := CancelTheTrains([1, 4], [2, 3, 5]);
  expect cancelled == 0, "impl test 3 failed";

  // Test 4: bottom=[1,2,3], left=[1,2,3] → 3
  cancelled := CancelTheTrains([1, 2, 3], [1, 2, 3]);
  expect cancelled == 3, "impl test 4 failed";

  // Test 5: bottom=[1,2,3,4,5], left=[1,2,3,4,5] → 5
  cancelled := CancelTheTrains([1, 2, 3, 4, 5], [1, 2, 3, 4, 5]);
  expect cancelled == 5, "impl test 5 failed";

  // Test 6: bottom=[3], left=[1,2,3,4,5] → 1
  cancelled := CancelTheTrains([3], [1, 2, 3, 4, 5]);
  expect cancelled == 1, "impl test 6 failed";

  // Test 7: bottom=[2,5,7,8], left=[6] → 0
  cancelled := CancelTheTrains([2, 5, 7, 8], [6]);
  expect cancelled == 0, "impl test 7 failed";

  // Test 8.1: bottom=[3,7], left=[3,7] → 2
  cancelled := CancelTheTrains([3, 7], [3, 7]);
  expect cancelled == 2, "impl test 8.1 failed";

  // Test 8.2: bottom=[5], left=[5] → 1
  cancelled := CancelTheTrains([5], [5]);
  expect cancelled == 1, "impl test 8.2 failed";

  // Test 9: bottom=[10,20,30], left=[5,10,20,40] → 2
  cancelled := CancelTheTrains([10, 20, 30], [5, 10, 20, 40]);
  expect cancelled == 2, "impl test 9 failed";

  // Test 10.1: bottom=[1], left=[1] → 1
  cancelled := CancelTheTrains([1], [1]);
  expect cancelled == 1, "impl test 10.1 failed";

  // Test 10.2: bottom=[1,2], left=[1,2] → 2
  cancelled := CancelTheTrains([1, 2], [1, 2]);
  expect cancelled == 2, "impl test 10.2 failed";

  // Test 10.3: bottom=[1,2,3], left=[4,5,6] → 0
  cancelled := CancelTheTrains([1, 2, 3], [4, 5, 6]);
  expect cancelled == 0, "impl test 10.3 failed";

  // Test 11: bottom=[2,4,8,15,23,50], left=[1,4,9,15,30,42,50] → 3
  cancelled := CancelTheTrains([2, 4, 8, 15, 23, 50], [1, 4, 9, 15, 30, 42, 50]);
  expect cancelled == 3, "impl test 11 failed";

  print "All tests passed\n";
}