function Abs(x: int): int
{
  if x >= 0 then x else -x
}

predicate HasAdjacentPair(a: seq<int>)
{
  exists i, j | 0 <= i < |a| && 0 <= j < |a| && i != j :: Abs(a[i] - a[j]) == 1
}

predicate ValidAssignment(a: seq<int>, assignment: seq<int>, numTeams: int)
{
  |assignment| == |a| &&
  numTeams >= 1 &&
  (forall i | 0 <= i < |a| :: 0 <= assignment[i] < numTeams) &&
  (forall i, j | 0 <= i < |a| && 0 <= j < |a| && i != j ::
    assignment[i] == assignment[j] ==> Abs(a[i] - a[j]) != 1)
}

function ConstantSeq(a: seq<int>, v: int): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else ConstantSeq(a[..|a|-1], v) + [v]
}

function ParityAssignment(a: seq<int>): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else ParityAssignment(a[..|a|-1]) + [a[|a|-1] % 2]
}

// Combined ensures predicate for spec testing
predicate MeetsSpec(a: seq<int>, teams: int)
{
  (teams == 1 || teams == 2) &&
  ValidAssignment(a, if teams == 1 then ConstantSeq(a, 0) else ParityAssignment(a), teams) &&
  (HasAdjacentPair(a) <==> teams == 2)
}

method YetAnotherDividingIntoTeams(a: seq<int>) returns (teams: int)
  requires forall i, j | 0 <= i < |a| && 0 <= j < |a| && i != j :: a[i] != a[j]
  requires forall i | 0 <= i < |a| :: 1 <= a[i] <= 100
  ensures teams == 1 || teams == 2
  ensures ValidAssignment(a, if teams == 1 then ConstantSeq(a, 0) else ParityAssignment(a), teams)
  ensures HasAdjacentPair(a) <==> teams == 2
{
  var b := new int[102];
  var i := 0;
  while i < 102 {
    b[i] := 0;
    i := i + 1;
  }
  i := 0;
  while i < |a| {
    if 0 <= a[i] < 102 {
      b[a[i]] := b[a[i]] + 1;
    }
    i := i + 1;
  }
  var flag := false;
  i := 1;
  while i <= 100 {
    if b[i] == 1 && (b[i + 1] == 1 || b[i - 1] == 1) {
      flag := true;
    }
    i := i + 1;
  }
  if flag {
    teams := 2;
  } else {
    teams := 1;
  }
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Small-input equivalents of each positive test pair, checking full ensures
  expect MeetsSpec([1], 1), "spec positive 1";           // from test 1.4: [42]->1
  expect MeetsSpec([1, 2], 2), "spec positive 2";        // from test 3.5: [1,2]->2
  expect MeetsSpec([1, 3], 1), "spec positive 3";        // from test 1.2: [3,6]->1
  expect MeetsSpec([2, 3, 4], 2), "spec positive 4";     // from test 1.3: [2,3,4,99,100]->2
  expect MeetsSpec([2, 1], 2), "spec positive 5";        // from test 3.2: [2,1]->2
  expect MeetsSpec([1, 2, 3], 2), "spec positive 6";     // from test 5.7: [1,2,3]->2
  expect MeetsSpec([1, 3, 5], 1), "spec positive 7";     // from test 6.1: [3,5,7]->1
  expect MeetsSpec([3, 4], 2), "spec positive 8";        // from test 3.8: [3,4,2,1]->2
  expect MeetsSpec([3, 2, 1], 2), "spec positive 9";     // from test 3.9: [3,2,1]->2
  expect MeetsSpec([1, 3, 2], 2), "spec positive 10";    // from test 5.5: [1,3,2]->2

  // ===== SPEC NEGATIVE TESTS =====
  // Small-input equivalents of each negative test pair, checking ensures rejects wrong output
  expect !MeetsSpec([1, 2], 3), "spec negative 1";       // from neg 1: wrong=3 (not 1 or 2)
  expect !MeetsSpec([1], 2), "spec negative 2";          // from neg 2: [100]->wrong 2, no adj pair
  expect !MeetsSpec([2, 1], 3), "spec negative 3";       // from neg 3: wrong=3 (not 1 or 2)
  expect !MeetsSpec([1, 3], 2), "spec negative 4";       // from neg 4: [1,31]->wrong 2, no adj pair
  expect !MeetsSpec([2], 2), "spec negative 5";          // from neg 5: [1]->wrong 2, no adj pair
  expect !MeetsSpec([1, 3, 5], 2), "spec negative 6";    // from neg 6: [3,5,7]->wrong 2, no adj pair
  expect !MeetsSpec([2, 4], 2), "spec negative 7";       // from neg 7: [99,97]->wrong 2, no adj pair

  // ===== IMPLEMENTATION TESTS =====
  var r: int;

  // Test 1
  r := YetAnotherDividingIntoTeams([2, 10, 1, 20]);
  expect r == 2, "impl test 1.1 failed";
  r := YetAnotherDividingIntoTeams([3, 6]);
  expect r == 1, "impl test 1.2 failed";
  r := YetAnotherDividingIntoTeams([2, 3, 4, 99, 100]);
  expect r == 2, "impl test 1.3 failed";
  r := YetAnotherDividingIntoTeams([42]);
  expect r == 1, "impl test 1.4 failed";

  // Test 2
  r := YetAnotherDividingIntoTeams([100]);
  expect r == 1, "impl test 2.1 failed";

  // Test 3
  r := YetAnotherDividingIntoTeams([3, 4, 1, 5, 2]);
  expect r == 2, "impl test 3.1 failed";
  r := YetAnotherDividingIntoTeams([2, 1]);
  expect r == 2, "impl test 3.2 failed";
  r := YetAnotherDividingIntoTeams([4, 1, 3, 2]);
  expect r == 2, "impl test 3.3 failed";
  r := YetAnotherDividingIntoTeams([2, 3, 1, 5, 4]);
  expect r == 2, "impl test 3.4 failed";
  r := YetAnotherDividingIntoTeams([1, 2]);
  expect r == 2, "impl test 3.5 failed";
  r := YetAnotherDividingIntoTeams([1, 2, 3, 4]);
  expect r == 2, "impl test 3.6 failed";
  r := YetAnotherDividingIntoTeams([1, 2]);
  expect r == 2, "impl test 3.7 failed";
  r := YetAnotherDividingIntoTeams([3, 4, 2, 1]);
  expect r == 2, "impl test 3.8 failed";
  r := YetAnotherDividingIntoTeams([3, 2, 1]);
  expect r == 2, "impl test 3.9 failed";
  r := YetAnotherDividingIntoTeams([1]);
  expect r == 1, "impl test 3.10 failed";

  // Test 4
  r := YetAnotherDividingIntoTeams([1, 31]);
  expect r == 1, "impl test 4.1 failed";

  // Test 5
  r := YetAnotherDividingIntoTeams([1]);
  expect r == 1, "impl test 5.1 failed";
  r := YetAnotherDividingIntoTeams([1]);
  expect r == 1, "impl test 5.2 failed";
  r := YetAnotherDividingIntoTeams([1]);
  expect r == 1, "impl test 5.3 failed";
  r := YetAnotherDividingIntoTeams([2, 1, 4, 3]);
  expect r == 2, "impl test 5.4 failed";
  r := YetAnotherDividingIntoTeams([1, 3, 2]);
  expect r == 2, "impl test 5.5 failed";
  r := YetAnotherDividingIntoTeams([1]);
  expect r == 1, "impl test 5.6 failed";
  r := YetAnotherDividingIntoTeams([1, 2, 3]);
  expect r == 2, "impl test 5.7 failed";
  r := YetAnotherDividingIntoTeams([1, 4, 2, 5, 3]);
  expect r == 2, "impl test 5.8 failed";
  r := YetAnotherDividingIntoTeams([4, 5, 2, 3, 1]);
  expect r == 2, "impl test 5.9 failed";
  r := YetAnotherDividingIntoTeams([4, 2, 3, 1]);
  expect r == 2, "impl test 5.10 failed";

  // Test 6
  r := YetAnotherDividingIntoTeams([3, 5, 7]);
  expect r == 1, "impl test 6.1 failed";

  // Test 7
  r := YetAnotherDividingIntoTeams([99, 97]);
  expect r == 1, "impl test 7.1 failed";

  print "All tests passed\n";
}