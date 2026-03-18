// --- Specification: Vus the Cossack and a Contest ---

function SumSeq(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else SumSeq(s[..|s|-1]) + s[|s|-1]
}

predicate AllAtLeastOne(s: seq<int>)
{
  forall i | 0 <= i < |s| :: s[i] >= 1
}

predicate ValidDistribution(dist: seq<int>, n: int, supply: int)
{
  n >= 0 &&
  |dist| == n &&
  AllAtLeastOne(dist) &&
  SumSeq(dist) <= supply
}

predicate ValidRewarding(penDist: seq<int>, noteDist: seq<int>, n: int, m: int, k: int)
{
  ValidDistribution(penDist, n, m) && ValidDistribution(noteDist, n, k)
}

function UniformDist(n: nat): (r: seq<int>)
  ensures |r| == n
  ensures forall i | 0 <= i < n :: r[i] == 1
  ensures SumSeq(r) == n
  decreases n
{
  if n == 0 then [] else UniformDist(n - 1) + [1]
}

function SumLowerBound(s: seq<int>): (b: bool)
  ensures AllAtLeastOne(s) ==> SumSeq(s) >= |s|
  decreases |s|
{
  if |s| == 0 then true
  else var _ := SumLowerBound(s[..|s|-1]); true
}

method VusContest(n: int, m: int, k: int) returns (result: string)
  requires n >= 1
  ensures result == "Yes" || result == "No"
  ensures result == "Yes" <==> ValidRewarding(UniformDist(n), UniformDist(n), n, m, k)
{
  if k < n || m < n {
    result := "No";
  } else {
    result := "Yes";
  }
}

// Encapsulates the ensures clause of VusContest for direct testability
predicate VusContestSpec(result: string, n: nat, m: int, k: int)
{
  (result == "Yes" || result == "No") &&
  ((result == "Yes") == ValidRewarding(UniformDist(n), UniformDist(n), n, m, k))
}

method Main() {
  // === SPEC POSITIVE TESTS ===
  // Each test pair scaled to small n (1-3) preserving the Yes/No answer.
  // Verifies the ensures clause holds for (correct_output, n, m, k).

  // Test 1: (5,8,6)->"Yes" scaled to (2,3,2)->"Yes"
  expect VusContestSpec("Yes", 2, 3, 2), "spec positive 1";
  // Test 2: (3,9,3)->"Yes" scaled to (3,5,3)->"Yes"
  expect VusContestSpec("Yes", 3, 5, 3), "spec positive 2";
  // Test 3: (8,5,20)->"No" scaled to (3,2,5)->"No"
  expect VusContestSpec("No", 3, 2, 5), "spec positive 3";
  // Test 4: (1,1,1)->"Yes" already small
  expect VusContestSpec("Yes", 1, 1, 1), "spec positive 4";
  // Test 5: (54,82,100)->"Yes" scaled to (2,3,4)->"Yes"
  expect VusContestSpec("Yes", 2, 3, 4), "spec positive 5";
  // Test 6: (1,100,100)->"Yes" scaled to (1,3,3)->"Yes"
  expect VusContestSpec("Yes", 1, 3, 3), "spec positive 6";
  // Test 7: (100,99,99)->"No" scaled to (3,2,2)->"No"
  expect VusContestSpec("No", 3, 2, 2), "spec positive 7";
  // Test 8: (8,20,5)->"No" scaled to (3,5,2)->"No"
  expect VusContestSpec("No", 3, 5, 2), "spec positive 8";
  // Test 9: (68,91,90)->"Yes" scaled to (2,4,3)->"Yes"
  expect VusContestSpec("Yes", 2, 4, 3), "spec positive 9";
  // Test 10: (92,35,39)->"No" scaled to (3,1,2)->"No"
  expect VusContestSpec("No", 3, 1, 2), "spec positive 10";

  // === SPEC NEGATIVE TESTS ===
  // Same scaled inputs with the WRONG output. Ensures clause must NOT hold.

  // Negative 1: (2,3,2) wrong "No" (correct "Yes")
  expect !VusContestSpec("No", 2, 3, 2), "spec negative 1";
  // Negative 2: (3,5,3) wrong "No" (correct "Yes")
  expect !VusContestSpec("No", 3, 5, 3), "spec negative 2";
  // Negative 3: (3,2,5) wrong "Yes" (correct "No")
  expect !VusContestSpec("Yes", 3, 2, 5), "spec negative 3";
  // Negative 4: (1,1,1) wrong "No" (correct "Yes")
  expect !VusContestSpec("No", 1, 1, 1), "spec negative 4";
  // Negative 5: (2,3,4) wrong "No" (correct "Yes")
  expect !VusContestSpec("No", 2, 3, 4), "spec negative 5";
  // Negative 6: (1,3,3) wrong "No" (correct "Yes")
  expect !VusContestSpec("No", 1, 3, 3), "spec negative 6";
  // Negative 7: (3,2,2) wrong "Yes" (correct "No")
  expect !VusContestSpec("Yes", 3, 2, 2), "spec negative 7";
  // Negative 8: (3,5,2) wrong "Yes" (correct "No")
  expect !VusContestSpec("Yes", 3, 5, 2), "spec negative 8";
  // Negative 9: (2,4,3) wrong "No" (correct "Yes")
  expect !VusContestSpec("No", 2, 4, 3), "spec negative 9";
  // Negative 10: (3,1,2) wrong "Yes" (correct "No")
  expect !VusContestSpec("Yes", 3, 1, 2), "spec negative 10";

  // === IMPLEMENTATION TESTS ===
  // Full-size inputs testing the method directly.

  var r1 := VusContest(5, 8, 6);
  expect r1 == "Yes", "impl test 1";

  var r2 := VusContest(3, 9, 3);
  expect r2 == "Yes", "impl test 2";

  var r3 := VusContest(8, 5, 20);
  expect r3 == "No", "impl test 3";

  var r4 := VusContest(1, 1, 1);
  expect r4 == "Yes", "impl test 4";

  var r5 := VusContest(54, 82, 100);
  expect r5 == "Yes", "impl test 5";

  var r6 := VusContest(1, 100, 100);
  expect r6 == "Yes", "impl test 6";

  var r7 := VusContest(100, 99, 99);
  expect r7 == "No", "impl test 7";

  var r8 := VusContest(8, 20, 5);
  expect r8 == "No", "impl test 8";

  var r9 := VusContest(68, 91, 90);
  expect r9 == "Yes", "impl test 9";

  var r10 := VusContest(92, 35, 39);
  expect r10 == "No", "impl test 10";

  print "All tests passed\n";
}