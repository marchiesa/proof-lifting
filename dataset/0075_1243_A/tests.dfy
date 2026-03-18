// --- Specification ---

function CountAtLeast(a: seq<int>, threshold: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[|a|-1] >= threshold then 1 else 0) + CountAtLeast(a[..|a|-1], threshold)
}

predicate IsAchievable(a: seq<int>, s: int)
{
  s >= 0 && CountAtLeast(a, s) >= s
}

predicate IsMaxSquareSide(a: seq<int>, side: int)
{
  IsAchievable(a, side) &&
  forall s | side < s <= |a| :: !IsAchievable(a, s)
}

// --- Implementation ---

method {:verify false} MaximumSquare(a: seq<int>) returns (side: int)
  ensures IsMaxSquareSide(a, side)
{
  var n := |a|;
  var arr := new int[n];
  var k := 0;
  while k < n {
    arr[k] := a[k];
    k := k + 1;
  }

  var i := 1;
  while i < n {
    var key := arr[i];
    var j := i - 1;
    while j >= 0 && arr[j] < key {
      arr[j + 1] := arr[j];
      j := j - 1;
    }
    arr[j + 1] := key;
    i := i + 1;
  }

  side := n;
  i := 0;
  while i < n {
    if arr[i] < i + 1 {
      side := i;
      return;
    }
    i := i + 1;
  }

  return;
}

method Main()
{
  // === SPEC POSITIVE TESTS (small inputs, length 1-3) ===

  // From Test 2 case 1: [1] -> 1
  expect IsMaxSquareSide([1], 1), "spec positive 1";

  // From Test 2 case 2: [2, 1] -> 1
  expect IsMaxSquareSide([2, 1], 1), "spec positive 2";

  // From Test 2 case 3: [3, 1, 2] -> 2
  expect IsMaxSquareSide([3, 1, 2], 2), "spec positive 3";

  // From Test 2 case 4: [2, 2, 2] -> 2
  expect IsMaxSquareSide([2, 2, 2], 2), "spec positive 4";

  // From Test 1 case 3: [1, 1, 1] -> 1
  expect IsMaxSquareSide([1, 1, 1], 1), "spec positive 5";

  // === SPEC NEGATIVE TESTS (small inputs, length 1-3) ===

  // From Negative 2 case 1: [1] -> wrong 2 (correct 1)
  expect !IsMaxSquareSide([1], 2), "spec negative 1";

  // Scaled from Negative 1 case 1: [4,3,1,4,5]->wrong 4; scaled to [3,1,2]->wrong 3 (correct 2)
  expect !IsMaxSquareSide([3, 1, 2], 3), "spec negative 2";

  // Wrong-low: [2, 1] -> wrong 0 (correct 1)
  expect !IsMaxSquareSide([2, 1], 0), "spec negative 3";

  // Wrong-high: [1, 1, 1] -> wrong 2 (correct 1)
  expect !IsMaxSquareSide([1, 1, 1], 2), "spec negative 4";

  // Wrong-low: [2, 2, 2] -> wrong 1 (correct 2)
  expect !IsMaxSquareSide([2, 2, 2], 1), "spec negative 5";

  // Wrong-high: [2, 1] -> wrong 2 (correct 1)
  expect !IsMaxSquareSide([2, 1], 2), "spec negative 6";

  // === IMPLEMENTATION TESTS (full-size inputs) ===

  // Test 1 cases
  var r1 := MaximumSquare([4, 3, 1, 4, 5]);
  expect r1 == 3, "impl test 1.1 failed";

  var r2 := MaximumSquare([4, 4, 4, 4]);
  expect r2 == 4, "impl test 1.2 failed";

  var r3 := MaximumSquare([1, 1, 1]);
  expect r3 == 1, "impl test 1.3 failed";

  var r4 := MaximumSquare([5, 5, 1, 1, 5]);
  expect r4 == 3, "impl test 1.4 failed";

  // Test 2 cases
  var r5 := MaximumSquare([1]);
  expect r5 == 1, "impl test 2.1 failed";

  var r6 := MaximumSquare([2, 1]);
  expect r6 == 1, "impl test 2.2 failed";

  var r7 := MaximumSquare([3, 1, 2]);
  expect r7 == 2, "impl test 2.3 failed";

  var r8 := MaximumSquare([2, 2, 2]);
  expect r8 == 2, "impl test 2.4 failed";

  var r9 := MaximumSquare([4, 1, 4, 1]);
  expect r9 == 2, "impl test 2.5 failed";

  var r10 := MaximumSquare([5, 4, 3, 2, 1]);
  expect r10 == 3, "impl test 2.6 failed";

  var r11 := MaximumSquare([1, 2, 3, 4, 5]);
  expect r11 == 3, "impl test 2.7 failed";

  var r12 := MaximumSquare([3, 2, 1, 6, 2, 2]);
  expect r12 == 2, "impl test 2.8 failed";

  var r13 := MaximumSquare([4, 5, 2, 9, 6, 10, 3, 7, 1, 8]);
  expect r13 == 5, "impl test 2.9 failed";

  var r14 := MaximumSquare([1, 3, 2, 2, 2, 9, 10, 10, 9, 7]);
  expect r14 == 5, "impl test 2.10 failed";

  print "All tests passed\n";
}