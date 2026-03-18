predicate AllLeqD(s: seq<int>, d: int) {
  forall i | 0 <= i < |s| :: s[i] <= d
}

predicate Reachable(s: seq<int>, d: int, steps: nat)
  decreases steps
{
  AllLeqD(s, d)
  || (steps > 0 && |s| >= 3
      && exists i: int, j: int, k: int
           | 0 <= i < |s| && 0 <= j < |s| && 0 <= k < |s|
             && i != j && i != k && j != k
           :: Reachable(s[i := s[j] + s[k]], d, steps - 1))
}

predicate CanMakeAllLeqD(a: seq<int>, d: int)
  requires |a| >= 3
{
  exists steps: nat | steps <= |a| - 2 :: Reachable(a, d, steps)
}

method ReplacingElements(a: seq<int>, d: int) returns (result: bool)
  requires |a| >= 3
  requires forall i | 0 <= i < |a| :: a[i] > 0
  ensures result == CanMakeAllLeqD(a, d)
{
  var n := |a|;
  var arr := new int[n];
  var i := 0;
  while i < n {
    arr[i] := a[i];
    i := i + 1;
  }

  // Selection sort
  i := 0;
  while i < n {
    var minIdx := i;
    var j := i + 1;
    while j < n {
      if arr[j] < arr[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    var tmp := arr[i];
    arr[i] := arr[minIdx];
    arr[minIdx] := tmp;
    i := i + 1;
  }

  if n < 2 {
    result := true;
    return;
  }

  if arr[1] > d {
    result := false;
    return;
  }

  i := 2;
  while i < n {
    var m := if arr[0] + arr[1] < arr[i] then arr[0] + arr[1] else arr[i];
    if m > d {
      result := false;
      return;
    }
    i := i + 1;
  }

  result := true;
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // Test pair 1 (scaled to length 3):
  //   [2,3,2,5,4] d=3 -> false  scaled to [2,2,4] d=3 -> false (min pair sum 4>3)
  //   [2,4,4] d=4 -> true       already length 3
  //   [2,1,5,3,6] d=4 -> true   scaled to [1,2,5] d=4 -> true (replace 5 with 1+2=3<=4)
  expect !CanMakeAllLeqD([2, 2, 4], 3), "spec positive 1a";
  expect CanMakeAllLeqD([2, 4, 4], 4), "spec positive 1b";
  expect CanMakeAllLeqD([1, 2, 5], 4), "spec positive 1c";

  // Test pair 2: [1,1,1] d=1 -> true
  expect CanMakeAllLeqD([1, 1, 1], 1), "spec positive 2";

  // Test pair 3: [1,1,1] d=1 -> true
  expect CanMakeAllLeqD([1, 1, 1], 1), "spec positive 3";

  // Test pair 4 (scaled): same distinct cases as pair 1
  expect !CanMakeAllLeqD([2, 2, 4], 3), "spec positive 4a";
  expect CanMakeAllLeqD([2, 4, 4], 4), "spec positive 4b";

  // Test pair 5: [3,3,3] d=3 -> true
  expect CanMakeAllLeqD([3, 3, 3], 3), "spec positive 5";

  // === SPEC NEGATIVE TESTS ===
  // Each negative pair corrupts the last case's output (flips true->false).
  // We verify the spec rejects the wrong output.

  // Neg 1: [2,1,5,3,6] d=4 correct=true, wrong=false; scaled to [1,2,5] d=4
  expect CanMakeAllLeqD([1, 2, 5], 4) != false, "spec negative 1";

  // Neg 2: [1,1,1] d=1 correct=true, wrong=false
  expect CanMakeAllLeqD([1, 1, 1], 1) != false, "spec negative 2";

  // Neg 3: [1,1,1] d=1 correct=true, wrong=false
  expect CanMakeAllLeqD([1, 1, 1], 1) != false, "spec negative 3";

  // Neg 4: [2,4,4] d=4 correct=true, wrong=false
  expect CanMakeAllLeqD([2, 4, 4], 4) != false, "spec negative 4";

  // Neg 5: [3,3,3] d=3 correct=true, wrong=false
  expect CanMakeAllLeqD([3, 3, 3], 3) != false, "spec negative 5";

  // === IMPLEMENTATION TESTS ===
  var r: bool;

  // Impl test 1 (3 cases)
  r := ReplacingElements([2, 3, 2, 5, 4], 3);
  expect r == false, "impl test 1.1 failed";
  r := ReplacingElements([2, 4, 4], 4);
  expect r == true, "impl test 1.2 failed";
  r := ReplacingElements([2, 1, 5, 3, 6], 4);
  expect r == true, "impl test 1.3 failed";

  // Impl test 2 (12 cases)
  var i := 0;
  while i < 12 {
    r := ReplacingElements([1, 1, 1], 1);
    expect r == true, "impl test 2 failed";
    i := i + 1;
  }

  // Impl test 3 (13 cases)
  i := 0;
  while i < 13 {
    r := ReplacingElements([1, 1, 1], 1);
    expect r == true, "impl test 3 failed";
    i := i + 1;
  }

  // Impl test 4 (11 cases: 3 full cycles + 2)
  i := 0;
  while i < 3 {
    r := ReplacingElements([2, 3, 2, 5, 4], 3);
    expect r == false, "impl test 4 NO failed";
    r := ReplacingElements([2, 4, 4], 4);
    expect r == true, "impl test 4 YES(1) failed";
    r := ReplacingElements([2, 1, 5, 3, 6], 4);
    expect r == true, "impl test 4 YES(2) failed";
    i := i + 1;
  }
  r := ReplacingElements([2, 3, 2, 5, 4], 3);
  expect r == false, "impl test 4.10 failed";
  r := ReplacingElements([2, 4, 4], 4);
  expect r == true, "impl test 4.11 failed";

  // Impl test 5 (15 cases)
  i := 0;
  while i < 15 {
    r := ReplacingElements([3, 3, 3], 3);
    expect r == true, "impl test 5 failed";
    i := i + 1;
  }

  print "All tests passed\n";
}