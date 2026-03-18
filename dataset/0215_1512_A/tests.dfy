function CountOccurrences(a: seq<int>, v: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else CountOccurrences(a[..|a|-1], v) + (if a[|a|-1] == v then 1 else 0)
}

predicate IsMajorityValue(a: seq<int>, v: int)
{
  CountOccurrences(a, v) == |a| - 1
}

predicate IsSpyIndex(a: seq<int>, idx: int)
{
  1 <= idx <= |a| &&
  exists k | 0 <= k < |a| :: IsMajorityValue(a, a[k]) && a[idx - 1] != a[k]
}

method SpyDetected(a: seq<int>) returns (idx: int)
  requires |a| >= 3
  requires forall i | 0 <= i < |a| :: a[i] > 0
  requires exists k | 0 <= k < |a| :: IsMajorityValue(a, a[k])
  ensures IsSpyIndex(a, idx)
{
  var i := 0;
  while i < |a|
  {
    var count := 0;
    var j := 0;
    while j < |a|
    {
      if a[j] == a[i] {
        count := count + 1;
      }
      j := j + 1;
    }
    if count == 1 {
      return i + 1;
    }
    i := i + 1;
  }
  return 0;
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // IsSpyIndex(a, idx) with correct idx on small inputs (scaled from test pairs)
  expect IsSpyIndex([1, 2, 1], 2), "spec positive 1";   // from Test 1
  expect IsSpyIndex([1, 2, 2], 1), "spec positive 2";   // from Test 2
  expect IsSpyIndex([1, 1, 2], 3), "spec positive 3";   // from Test 3
  expect IsSpyIndex([2, 2, 3], 3), "spec positive 4";   // from Test 4
  expect IsSpyIndex([4, 1, 4], 2), "spec positive 5";   // from Test 5
  expect IsSpyIndex([3, 1, 3], 2), "spec positive 6";   // from Test 6
  expect IsSpyIndex([5, 1, 5], 2), "spec positive 7";   // from Test 7
  expect IsSpyIndex([3, 3, 2], 3), "spec positive 8";   // from Test 8
  expect IsSpyIndex([2, 2, 1], 3), "spec positive 9";   // from Test 9
  expect IsSpyIndex([2, 1, 2], 2), "spec positive 10";  // from Test 10

  // ===== SPEC NEGATIVE TESTS =====
  // IsSpyIndex(a, wrong_idx) must be false (scaled from negative pairs)
  expect !IsSpyIndex([1, 2, 1], 3), "spec negative 1";  // wrong: majority elem
  expect !IsSpyIndex([1, 2, 2], 2), "spec negative 2";  // wrong: majority elem
  expect !IsSpyIndex([1, 1, 2], 4), "spec negative 3";  // wrong: out of bounds
  expect !IsSpyIndex([2, 2, 3], 1), "spec negative 4";  // wrong: majority elem
  expect !IsSpyIndex([2, 1, 2], 1), "spec negative 5";  // wrong: majority elem
  expect !IsSpyIndex([3, 1, 3], 3), "spec negative 6";  // wrong: majority elem
  expect !IsSpyIndex([5, 1, 5], 3), "spec negative 7";  // wrong: majority elem
  expect !IsSpyIndex([3, 3, 2], 1), "spec negative 8";  // wrong: majority elem
  expect !IsSpyIndex([1, 1, 2], 2), "spec negative 9";  // wrong: majority elem
  expect !IsSpyIndex([2, 1, 2], 3), "spec negative 10"; // wrong: majority elem

  // ===== IMPLEMENTATION TESTS =====
  // Test 1
  var r1 := SpyDetected([11, 13, 11, 11]);
  expect r1 == 2, "impl test 1a failed";
  var r2 := SpyDetected([1, 4, 4, 4, 4]);
  expect r2 == 1, "impl test 1b failed";
  var r3 := SpyDetected([3, 3, 3, 3, 10, 3, 3, 3, 3, 3]);
  expect r3 == 5, "impl test 1c failed";
  var r4 := SpyDetected([20, 20, 10]);
  expect r4 == 3, "impl test 1d failed";

  // Test 2
  var r5 := SpyDetected([5, 6, 6]);
  expect r5 == 1, "impl test 2a failed";
  var r6 := SpyDetected([7, 7, 6]);
  expect r6 == 3, "impl test 2b failed";

  // Test 3
  var r7 := SpyDetected([5, 5, 1]);
  expect r7 == 3, "impl test 3a failed";
  var r8 := SpyDetected([2, 2, 2, 7]);
  expect r8 == 4, "impl test 3b failed";
  var r9 := SpyDetected([9, 3, 9]);
  expect r9 == 2, "impl test 3c failed";

  // Test 4
  var r10 := SpyDetected([6, 6, 6, 6, 3]);
  expect r10 == 5, "impl test 4 failed";

  // Test 5
  var r11 := SpyDetected([1, 2, 1]);
  expect r11 == 2, "impl test 5a failed";
  var r12 := SpyDetected([4, 4, 4, 4, 4, 9]);
  expect r12 == 6, "impl test 5b failed";

  // Test 6
  var r13 := SpyDetected([8, 8, 8, 1, 8, 8, 8]);
  expect r13 == 4, "impl test 6 failed";

  // Test 7
  var r14 := SpyDetected([50, 10, 50]);
  expect r14 == 2, "impl test 7 failed";

  // Test 8
  var r15 := SpyDetected([3, 3, 7, 3]);
  expect r15 == 3, "impl test 8a failed";
  var r16 := SpyDetected([2, 2, 2, 5, 2]);
  expect r16 == 4, "impl test 8b failed";

  // Test 9
  var r17 := SpyDetected([1, 1, 1, 1, 1, 1, 1, 1, 1, 7]);
  expect r17 == 10, "impl test 9 failed";

  // Test 10
  var r18 := SpyDetected([4, 9, 4]);
  expect r18 == 2, "impl test 10 failed";

  // Test 11
  var r19 := SpyDetected([11, 11, 11, 11, 2]);
  expect r19 == 5, "impl test 11a failed";
  var r20 := SpyDetected([6, 1, 6]);
  expect r20 == 2, "impl test 11b failed";
  var r21 := SpyDetected([3, 3, 3, 8]);
  expect r21 == 4, "impl test 11c failed";

  // Test 12
  var r22 := SpyDetected([5, 5, 5, 5, 5, 2]);
  expect r22 == 6, "impl test 12 failed";

  print "All tests passed\n";
}