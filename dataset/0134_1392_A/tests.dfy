predicate CanReduce(a: seq<int>, steps: nat)
  decreases steps
{
  if steps == 0 then
    true
  else if |a| < 2 then
    false
  else
    exists i | 0 <= i < |a| - 1 ::
      a[i] != a[i+1] && CanReduce(a[..i] + [a[i] + a[i+1]] + a[i+2..], steps - 1)
}

predicate MeetsSpec(a: seq<int>, result: int)
{
  |a| >= 1 &&
  1 <= result <= |a| &&
  CanReduce(a, |a| - result) &&
  (result == 1 || !CanReduce(a, |a| - result + 1))
}

method OmkarAndPassword(a: seq<int>) returns (result: int)
  requires |a| >= 1
  ensures 1 <= result <= |a|
  ensures CanReduce(a, |a| - result)
  ensures result == 1 || !CanReduce(a, |a| - result + 1)
{
  var lo := a[0];
  var hi := a[0];
  var i := 1;
  while i < |a|
  {
    if a[i] < lo { lo := a[i]; }
    if a[i] > hi { hi := a[i]; }
    i := i + 1;
  }
  if lo == hi {
    return |a|;
  } else {
    return 1;
  }
}

method Main()
{
  var r: int;

  // ===== SPEC POSITIVE TESTS =====
  // Small-input equivalents of the positive test pairs
  expect MeetsSpec([5], 1), "spec positive 1";          // single element
  expect MeetsSpec([1, 1], 2), "spec positive 2";       // all-equal pair (from [420,420]->2)
  expect MeetsSpec([1, 2], 1), "spec positive 3";       // mixed pair (from [420,69]->1)
  expect MeetsSpec([1, 1, 1], 3), "spec positive 4";    // all-equal triple (from [16,16,16]->3)
  expect MeetsSpec([1, 2, 3], 1), "spec positive 5";    // mixed triple (Test 8)
  expect MeetsSpec([3, 1, 2], 1), "spec positive 6";    // mixed triple (Test 6)
  expect MeetsSpec([1, 2, 1], 1), "spec positive 7";    // mixed triple (from [1,2,1,2]->1)

  // ===== SPEC NEGATIVE TESTS =====
  // Small-input equivalents of the negative test pairs with wrong outputs
  expect !MeetsSpec([1, 2], 2), "spec negative 1";      // Neg1: mixed, wrong=|a|
  expect !MeetsSpec([1, 2, 1], 2), "spec negative 2";   // Neg2/5: mixed, wrong=2
  expect !MeetsSpec([1, 1], 3), "spec negative 3";      // Neg3: all-equal, wrong>|a|
  expect !MeetsSpec([1, 2, 3], 2), "spec negative 4";   // Neg4/8/9: mixed triple, wrong=2
  expect !MeetsSpec([3, 1, 2], 2), "spec negative 5";   // Neg6: mixed triple, wrong=2
  expect !MeetsSpec([1, 1, 2], 2), "spec negative 6";   // Neg7: mixed, wrong=2
  expect !MeetsSpec([1, 1, 1], 2), "spec negative 7";   // all-equal, wrong<|a|

  // ===== IMPLEMENTATION TESTS =====
  // Test 1
  r := OmkarAndPassword([2, 1, 3, 1]);
  expect r == 1, "impl test 1a failed";
  r := OmkarAndPassword([420, 420]);
  expect r == 2, "impl test 1b failed";

  // Test 2
  r := OmkarAndPassword([1, 7, 7, 1, 7, 1]);
  expect r == 1, "impl test 2a failed";
  r := OmkarAndPassword([3, 3]);
  expect r == 2, "impl test 2b failed";
  r := OmkarAndPassword([1, 1000000000, 1000000000, 2, 2, 1, 2, 2]);
  expect r == 1, "impl test 2c failed";
  r := OmkarAndPassword([420, 69]);
  expect r == 1, "impl test 2d failed";
  r := OmkarAndPassword([1, 3, 5, 7, 9, 2, 4, 6, 8, 10]);
  expect r == 1, "impl test 2e failed";
  r := OmkarAndPassword([6, 16, 7, 6, 1]);
  expect r == 1, "impl test 2f failed";
  r := OmkarAndPassword([16, 16, 16]);
  expect r == 3, "impl test 2g failed";
  r := OmkarAndPassword([1, 2, 9, 8, 4]);
  expect r == 1, "impl test 2h failed";

  // Test 3
  r := OmkarAndPassword([529035968, 529035968, 529035968, 529035968, 529035968, 529035968, 529035968]);
  expect r == 7, "impl test 3 failed";

  // Test 4
  r := OmkarAndPassword([3, 4, 7]);
  expect r == 1, "impl test 4 failed";

  // Test 5
  r := OmkarAndPassword([1, 2, 1, 2]);
  expect r == 1, "impl test 5 failed";

  // Test 6
  r := OmkarAndPassword([3, 1, 2]);
  expect r == 1, "impl test 6 failed";

  // Test 7
  r := OmkarAndPassword([4, 4, 2, 2]);
  expect r == 1, "impl test 7 failed";

  // Test 8
  r := OmkarAndPassword([1, 2, 3]);
  expect r == 1, "impl test 8 failed";

  // Test 9
  r := OmkarAndPassword([2, 4, 6, 10]);
  expect r == 1, "impl test 9 failed";

  // Test 10
  r := OmkarAndPassword([5, 4, 9, 9, 9]);
  expect r == 1, "impl test 10 failed";

  // Test 11
  r := OmkarAndPassword([2, 2, 3, 3, 3]);
  expect r == 1, "impl test 11 failed";

  // Test 12
  r := OmkarAndPassword([3, 4, 4, 4]);
  expect r == 1, "impl test 12 failed";

  // Test 13
  r := OmkarAndPassword([4, 1, 5, 5, 5, 5]);
  expect r == 1, "impl test 13 failed";

  // Test 14
  r := OmkarAndPassword([1, 1, 2, 4]);
  expect r == 1, "impl test 14 failed";

  // Test 15
  r := OmkarAndPassword([1, 1, 1, 1, 1, 1, 1, 1, 1, 2]);
  expect r == 1, "impl test 15 failed";

  // Test 16
  r := OmkarAndPassword([5, 5, 5, 3, 2]);
  expect r == 1, "impl test 16 failed";

  // Test 17
  r := OmkarAndPassword([1, 2, 3, 4, 11]);
  expect r == 1, "impl test 17 failed";

  // Test 18
  r := OmkarAndPassword([1, 3, 4]);
  expect r == 1, "impl test 18 failed";

  // Test 19
  r := OmkarAndPassword([2, 2, 1, 2, 2]);
  expect r == 1, "impl test 19 failed";

  // Test 20
  r := OmkarAndPassword([5, 6, 11, 11, 11]);
  expect r == 1, "impl test 20 failed";

  print "All tests passed\n";
}