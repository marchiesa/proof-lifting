predicate IsSubsequence(c: seq<int>, s: seq<int>)
  decreases |s|
{
  if |c| == 0 then true
  else if |s| == 0 then false
  else if c[|c|-1] == s[|s|-1] then IsSubsequence(c[..|c|-1], s[..|s|-1])
  else IsSubsequence(c, s[..|s|-1])
}

predicate ExistsCommonSubseqOfLen(a: seq<int>, b: seq<int>, k: nat)
  decreases |a| + |b|
{
  if k == 0 then true
  else if |a| == 0 || |b| == 0 then false
  else if a[|a|-1] == b[|b|-1] then
    ExistsCommonSubseqOfLen(a[..|a|-1], b[..|b|-1], k - 1) ||
    ExistsCommonSubseqOfLen(a[..|a|-1], b, k) ||
    ExistsCommonSubseqOfLen(a, b[..|b|-1], k)
  else
    ExistsCommonSubseqOfLen(a[..|a|-1], b, k) ||
    ExistsCommonSubseqOfLen(a, b[..|b|-1], k)
}

function Min(x: nat, y: nat): nat {
  if x <= y then x else y
}

predicate PostCondition(found: bool, c: seq<int>, a: seq<int>, b: seq<int>)
{
  (found ==>
    |c| >= 1 &&
    IsSubsequence(c, a) &&
    IsSubsequence(c, b) &&
    forall len | 1 <= len < |c| :: !ExistsCommonSubseqOfLen(a, b, len))
  &&
  (!found ==>
    forall len | 1 <= len <= Min(|a|, |b|) :: !ExistsCommonSubseqOfLen(a, b, len))
}

method CommonSubsequence(a: seq<int>, b: seq<int>) returns (found: bool, c: seq<int>)
  ensures found ==>
    |c| >= 1 &&
    IsSubsequence(c, a) &&
    IsSubsequence(c, b) &&
    forall len | 1 <= len < |c| :: !ExistsCommonSubseqOfLen(a, b, len)
  ensures !found ==>
    forall len | 1 <= len <= Min(|a|, |b|) :: !ExistsCommonSubseqOfLen(a, b, len)
{
  found := false;
  c := [];
  var i := 0;
  while i < |a|
  {
    var j := 0;
    while j < |b|
    {
      if a[i] == b[j] {
        found := true;
        c := [a[i]];
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // PostCondition with correct (found, c) for small-input equivalents of each positive test pair

  // Spec positive 1 (Test 1 Case 2 scaled: a=[3], b=[3] -> found=true, c=[3])
  expect PostCondition(true, [3], [3], [3]), "spec positive 1";

  // Spec positive 2 (Test 1 Case 3: a=[3], b=[2] -> found=false)
  expect PostCondition(false, [], [3], [2]), "spec positive 2";

  // Spec positive 3 (Test 4 scaled: a=[5], b=[5] -> found=true, c=[5])
  expect PostCondition(true, [5], [5], [5]), "spec positive 3";

  // Spec positive 4 (Test 5 scaled: a=[1,2], b=[1,2] -> found=true, c=[1])
  expect PostCondition(true, [1], [1, 2], [1, 2]), "spec positive 4";

  // Spec positive 5 (Test 7: a=[1,1], b=[1,2] -> found=true, c=[1])
  expect PostCondition(true, [1], [1, 1], [1, 2]), "spec positive 5";

  // Spec positive 6 (Test 2: a=[1,1], b=[1,2,3] -> found=true, c=[1])
  expect PostCondition(true, [1], [1, 1], [1, 2, 3]), "spec positive 6";

  // Spec positive 7 (Test 3: a=[2,2], b=[2,2] -> found=true, c=[2])
  expect PostCondition(true, [2], [2, 2], [2, 2]), "spec positive 7";

  // ===== SPEC NEGATIVE TESTS =====
  // PostCondition with WRONG outputs — should all be rejected

  // Spec negative 1 (Neg 1 scaled: a=[1,2], b=[1,2], wrong: found=true, c=[3] — 3 not in either)
  expect !PostCondition(true, [3], [1, 2], [1, 2]), "spec negative 1";

  // Spec negative 2 (Neg 2: a=[1,1], b=[1,2,3], wrong: found=false — they share 1)
  expect !PostCondition(false, [], [1, 1], [1, 2, 3]), "spec negative 2";

  // Spec negative 3 (Neg 3: a=[2,2], b=[2,2], wrong: found=true, c=[3] — 3 not in either)
  expect !PostCondition(true, [3], [2, 2], [2, 2]), "spec negative 3";

  // Spec negative 4 (Neg 4 scaled: a=[5], b=[5], wrong: found=true, c=[4] — 4 not in either)
  expect !PostCondition(true, [4], [5], [5]), "spec negative 4";

  // Spec negative 5 (Neg 5 scaled: a=[3], b=[1,2,3], wrong: found=false — they share 3)
  expect !PostCondition(false, [], [3], [1, 2, 3]), "spec negative 5";

  // Spec negative 6 (Neg 6 scaled: a=[1,1,1], b=[1,2,3], wrong: found=false — they share 1)
  expect !PostCondition(false, [], [1, 1, 1], [1, 2, 3]), "spec negative 6";

  // Spec negative 7 (Neg 7: a=[1,1], b=[1,2], wrong: found=true, c=[0] — 0 not in either)
  expect !PostCondition(true, [0], [1, 1], [1, 2]), "spec negative 7";

  // ===== IMPLEMENTATION TESTS =====

  var found1, c1 := CommonSubsequence([10, 8, 6, 4], [1, 2, 3, 4, 5]);
  expect found1 == true, "impl test 1 failed";
  expect c1 == [4], "impl test 1 failed";

  var found2, c2 := CommonSubsequence([3], [3]);
  expect found2 == true, "impl test 2 failed";
  expect c2 == [3], "impl test 2 failed";

  var found3, c3 := CommonSubsequence([3], [2]);
  expect found3 == false, "impl test 3 failed";

  var found4, c4 := CommonSubsequence([1000, 2, 2, 2, 3], [3, 1, 5]);
  expect found4 == true, "impl test 4 failed";
  expect c4 == [3], "impl test 4 failed";

  var found5, c5 := CommonSubsequence([1, 2, 3, 4, 5], [1, 2, 3, 4, 5]);
  expect found5 == true, "impl test 5 failed";
  expect c5 == [1], "impl test 5 failed";

  var found6, c6 := CommonSubsequence([1, 1], [1, 2, 3]);
  expect found6 == true, "impl test 6 failed";
  expect c6 == [1], "impl test 6 failed";

  var found7, c7 := CommonSubsequence([2, 2], [2, 2]);
  expect found7 == true, "impl test 7 failed";
  expect c7 == [2], "impl test 7 failed";

  var found8, c8 := CommonSubsequence([1000], [1000]);
  expect found8 == true, "impl test 8 failed";
  expect c8 == [1000], "impl test 8 failed";

  var found9, c9 := CommonSubsequence([3], [1, 2, 3]);
  expect found9 == true, "impl test 9 failed";
  expect c9 == [3], "impl test 9 failed";

  var found10, c10 := CommonSubsequence([1, 1, 1, 1], [1, 2, 3, 4]);
  expect found10 == true, "impl test 10 failed";
  expect c10 == [1], "impl test 10 failed";

  var found11, c11 := CommonSubsequence([1, 1], [1, 2]);
  expect found11 == true, "impl test 11 failed";
  expect c11 == [1], "impl test 11 failed";

  print "All tests passed\n";
}