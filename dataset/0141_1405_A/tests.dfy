predicate InRange(s: seq<int>)
{
  forall i | 0 <= i < |s| :: 1 <= s[i] <= |s|
}

predicate AllDistinct(s: seq<int>)
{
  forall i, j | 0 <= i < |s| && 0 <= j < |s| && i != j :: s[i] != s[j]
}

predicate IsPermutation(p: seq<int>)
{
  InRange(p) && AllDistinct(p)
}

function AdjacentSums(p: seq<int>): seq<int>
  decreases |p|
{
  if |p| < 2 then []
  else if |p| == 2 then [p[0] + p[1]]
  else [p[0] + p[1]] + AdjacentSums(p[1..])
}

predicate SameFingerprint(p: seq<int>, q: seq<int>)
{
  multiset(AdjacentSums(p)) == multiset(AdjacentSums(q))
}

predicate MeetsSpec(p: seq<int>, p': seq<int>)
{
  |p'| == |p| && IsPermutation(p') && p' != p && SameFingerprint(p, p')
}

method PermutationForgery(p: seq<int>) returns (p': seq<int>)
  requires |p| >= 2
  requires IsPermutation(p)
  ensures |p'| == |p|
  ensures IsPermutation(p')
  ensures p' != p
  ensures SameFingerprint(p, p')
{
  p' := [];
  var i := |p|;
  while i > 0
  {
    i := i - 1;
    p' := p' + [p[i]];
  }
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // From Test 2: [1,2] -> [2,1]
  expect MeetsSpec([1, 2], [2, 1]), "spec positive 1";

  // From Test 3: [1,3,2] -> [2,3,1]
  expect MeetsSpec([1, 3, 2], [2, 3, 1]), "spec positive 2";

  // From Test 10: [2,1] -> [1,2]
  expect MeetsSpec([2, 1], [1, 2]), "spec positive 3";

  // From Test 10: [2,3,1] -> [1,3,2]
  expect MeetsSpec([2, 3, 1], [1, 3, 2]), "spec positive 4";

  // From Test 7: [3,1,2] -> [2,1,3]
  expect MeetsSpec([3, 1, 2], [2, 1, 3]), "spec positive 5";

  // === SPEC NEGATIVE TESTS ===
  // From Negative 1/2: [1,2] -> wrong [3,1]
  expect !MeetsSpec([1, 2], [3, 1]), "spec negative 1";

  // From Negative 3: [1,3,2] -> wrong [3,3,1]
  expect !MeetsSpec([1, 3, 2], [3, 3, 1]), "spec negative 2";

  // From Negative 7: [3,1,2] -> wrong [3,1,3]
  expect !MeetsSpec([3, 1, 2], [3, 1, 3]), "spec negative 3";

  // From Negative 10: [2,1] -> wrong [2,2]
  expect !MeetsSpec([2, 1], [2, 2]), "spec negative 4";

  // From Negative 4: [1,4,2,3] -> wrong [4,2,4,1]
  expect !MeetsSpec([1, 4, 2, 3], [4, 2, 4, 1]), "spec negative 5";

  // === IMPLEMENTATION TESTS ===
  var r1 := PermutationForgery([1, 2]);
  expect r1 == [2, 1], "impl test 1 failed";

  var r2 := PermutationForgery([2, 1, 6, 5, 4, 3]);
  expect r2 == [3, 4, 5, 6, 1, 2], "impl test 2 failed";

  var r3 := PermutationForgery([2, 4, 3, 1, 5]);
  expect r3 == [5, 1, 3, 4, 2], "impl test 3 failed";

  var r4 := PermutationForgery([1, 3, 2]);
  expect r4 == [2, 3, 1], "impl test 4 failed";

  var r5 := PermutationForgery([1, 4, 2, 3]);
  expect r5 == [3, 2, 4, 1], "impl test 5 failed";

  var r6 := PermutationForgery([3, 1, 2]);
  expect r6 == [2, 1, 3], "impl test 6 failed";

  var r7 := PermutationForgery([4, 1, 3, 2]);
  expect r7 == [2, 3, 1, 4], "impl test 7 failed";

  var r8 := PermutationForgery([1, 2, 3, 4, 5, 6, 7]);
  expect r8 == [7, 6, 5, 4, 3, 2, 1], "impl test 8 failed";

  var r9 := PermutationForgery([8, 6, 4, 2, 1, 3, 5, 7]);
  expect r9 == [7, 5, 3, 1, 2, 4, 6, 8], "impl test 9 failed";

  var r10 := PermutationForgery([2, 1]);
  expect r10 == [1, 2], "impl test 10 failed";

  var r11 := PermutationForgery([2, 3, 1]);
  expect r11 == [1, 3, 2], "impl test 11 failed";

  var r12 := PermutationForgery([3, 1, 4, 2]);
  expect r12 == [2, 4, 1, 3], "impl test 12 failed";

  var r13 := PermutationForgery([5, 3, 1, 2, 4]);
  expect r13 == [4, 2, 1, 3, 5], "impl test 13 failed";

  var r14 := PermutationForgery([6, 1, 5, 2, 4, 3]);
  expect r14 == [3, 4, 2, 5, 1, 6], "impl test 14 failed";

  print "All tests passed\n";
}