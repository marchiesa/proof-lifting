// === Formal Specification ===

function SumSeq(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else SumSeq(s[..|s|-1]) + s[|s|-1]
}

function CoalitionSeatSum(a: seq<int>, coalition: seq<int>): int
  decreases |coalition|
{
  if |coalition| == 0 then 0
  else if 1 <= coalition[|coalition|-1] <= |a|
    then CoalitionSeatSum(a, coalition[..|coalition|-1]) + a[coalition[|coalition|-1] - 1]
    else CoalitionSeatSum(a, coalition[..|coalition|-1])
}

predicate IsValidCoalition(n: int, a: seq<int>, coalition: seq<int>)
  requires |a| == n >= 1
{
  (forall i | 0 <= i < |coalition| :: 1 <= coalition[i] <= n) &&
  (forall i, j | 0 <= i < |coalition| && 0 <= j < |coalition| && i != j :: coalition[i] != coalition[j]) &&
  (exists i | 0 <= i < |coalition| :: coalition[i] == 1) &&
  (forall i | 0 <= i < |coalition| :: coalition[i] == 1 || a[0] >= 2 * a[coalition[i] - 1]) &&
  CoalitionSeatSum(a, coalition) * 2 > SumSeq(a)
}

function EligibleSum(a: seq<int>): int
  requires |a| >= 1
  decreases |a|
{
  if |a| == 1 then a[0]
  else if a[|a| - 1] * 2 <= a[0] then EligibleSum(a[..|a| - 1]) + a[|a| - 1]
  else EligibleSum(a[..|a| - 1])
}

predicate NoValidCoalitionPossible(n: int, a: seq<int>)
  requires |a| == n >= 1
{
  EligibleSum(a) * 2 <= SumSeq(a)
}

// === Implementation ===

method PrimeMinister(n: int, a: seq<int>) returns (k: int, coalition: seq<int>)
  requires n >= 1
  requires |a| == n
  requires forall i | 0 <= i < n :: a[i] >= 0
  ensures k > 0 ==> (k == |coalition| && IsValidCoalition(n, a, coalition))
  ensures k == 0 ==> (coalition == [] && NoValidCoalitionPossible(n, a))
{
  var c: seq<int> := [1];
  var coalitionSum := a[0];
  var i := 1;
  while i < n
  {
    if a[0] >= 2 * a[i] {
      c := c + [i + 1];
      coalitionSum := coalitionSum + a[i];
    }
    i := i + 1;
  }
  var totalSum := 0;
  i := 0;
  while i < n
  {
    totalSum := totalSum + a[i];
    i := i + 1;
  }
  if coalitionSum * 2 > totalSum {
    k := |c|;
    coalition := c;
  } else {
    k := 0;
    coalition := [];
  }
}

// === Tests ===

method Main() {
  // ============================================================
  // SPEC POSITIVE TESTS (small scaled-down inputs)
  // ============================================================

  // SP1 (Test 1 scaled: [100,50,50]->[4,2,2]): all 3 parties form valid coalition
  expect 3 == |[1,2,3]| && IsValidCoalition(3, [4,2,2], [1,2,3]),
    "spec positive 1";

  // SP2 (Test 2 scaled: [80,60,60]->[4,3,3]): no valid coalition possible
  expect NoValidCoalitionPossible(3, [4,3,3]),
    "spec positive 2";

  // SP3 (Test 3 scaled: [6,5]->[3,2]): Alice alone has strict majority
  expect 1 == |[1]| && IsValidCoalition(2, [3,2], [1]),
    "spec positive 3";

  // SP4 (Test 4 scaled: [51,25,99,25]->[4,2,3]): skip ineligible party 3
  expect 2 == |[1,2]| && IsValidCoalition(3, [4,2,3], [1,2]),
    "spec positive 4";

  // SP5 (Test 6 scaled: [100,100]->[5,5]): no majority possible
  expect NoValidCoalitionPossible(2, [5,5]),
    "spec positive 5";

  // SP6 (Test 7: already small): n=2, a=[1,1], no majority
  expect NoValidCoalitionPossible(2, [1,1]),
    "spec positive 6";

  // SP7 (Test 8 scaled: [50,25,25,100]->[2,1,4]): no majority possible
  expect NoValidCoalitionPossible(3, [2,1,4]),
    "spec positive 7";

  // SP8 (Test 9 scaled: [51,26,26]->[3,2,2]): no majority
  expect NoValidCoalitionPossible(3, [3,2,2]),
    "spec positive 8";

  // SP9 (Test 10: already small): n=3, a=[1,1,1], no majority
  expect NoValidCoalitionPossible(3, [1,1,1]),
    "spec positive 9";

  // ============================================================
  // SPEC NEGATIVE TESTS (small scaled-down inputs, wrong outputs)
  // ============================================================

  // SN1 (Neg 1 scaled): wrong k=4 but |coalition|=3, k mismatch
  expect !(4 == |[1,2,3]| && IsValidCoalition(3, [4,2,2], [1,2,3])),
    "spec negative 1";

  // SN2 (Neg 2 scaled): wrong k=1 with coalition=[1], Alice alone lacks majority in [4,3,3]
  expect !(1 == |[1]| && IsValidCoalition(3, [4,3,3], [1])),
    "spec negative 2";

  // SN3 (Neg 3 scaled): wrong k=2 but |coalition|=1, k mismatch
  expect !(2 == |[1]| && IsValidCoalition(2, [3,2], [1])),
    "spec negative 3";

  // SN4 (Neg 4 scaled): wrong k=3 but |coalition|=2, k mismatch
  expect !(3 == |[1,2]| && IsValidCoalition(3, [4,2,3], [1,2])),
    "spec negative 4";

  // SN5 (Neg 6 scaled): wrong k=1 with coalition=[1], no majority in [5,5]
  expect !(1 == |[1]| && IsValidCoalition(2, [5,5], [1])),
    "spec negative 5";

  // SN6 (Neg 7: already small): wrong k=1 with coalition=[1], no majority in [1,1]
  expect !(1 == |[1]| && IsValidCoalition(2, [1,1], [1])),
    "spec negative 6";

  // SN7 (Neg 8 scaled): wrong k=1 with coalition=[1], no majority in [2,1,4]
  expect !(1 == |[1]| && IsValidCoalition(3, [2,1,4], [1])),
    "spec negative 7";

  // SN8 (Neg 9 scaled): wrong k=1 with coalition=[1], no majority in [3,2,2]
  expect !(1 == |[1]| && IsValidCoalition(3, [3,2,2], [1])),
    "spec negative 8";

  // SN9 (Neg 10: already small): wrong k=1 with coalition=[1], no majority in [1,1,1]
  expect !(1 == |[1]| && IsValidCoalition(3, [1,1,1], [1])),
    "spec negative 9";

  // ============================================================
  // IMPLEMENTATION TESTS (full-size inputs)
  // ============================================================

  var k1, c1 := PrimeMinister(3, [100, 50, 50]);
  expect k1 == 3 && c1 == [1, 2, 3], "impl test 1";

  var k2, c2 := PrimeMinister(3, [80, 60, 60]);
  expect k2 == 0 && c2 == [], "impl test 2";

  var k3, c3 := PrimeMinister(2, [6, 5]);
  expect k3 == 1 && c3 == [1], "impl test 3";

  var k4, c4 := PrimeMinister(4, [51, 25, 99, 25]);
  expect k4 == 3 && c4 == [1, 2, 4], "impl test 4";

  // Test 5: n=100, a=[2,1,1,...,1] -> k=100, coalition=[1..100]
  var a5: seq<int> := [2];
  var idx := 1;
  while idx < 100 {
    a5 := a5 + [1];
    idx := idx + 1;
  }
  var exp5: seq<int> := [];
  idx := 1;
  while idx <= 100 {
    exp5 := exp5 + [idx];
    idx := idx + 1;
  }
  var k5, c5 := PrimeMinister(100, a5);
  expect k5 == 100 && c5 == exp5, "impl test 5";

  var k6, c6 := PrimeMinister(2, [100, 100]);
  expect k6 == 0 && c6 == [], "impl test 6";

  var k7, c7 := PrimeMinister(2, [1, 1]);
  expect k7 == 0 && c7 == [], "impl test 7";

  var k8, c8 := PrimeMinister(4, [50, 25, 25, 100]);
  expect k8 == 0 && c8 == [], "impl test 8";

  var k9, c9 := PrimeMinister(3, [51, 26, 26]);
  expect k9 == 0 && c9 == [], "impl test 9";

  var k10, c10 := PrimeMinister(3, [1, 1, 1]);
  expect k10 == 0 && c10 == [], "impl test 10";

  print "All tests passed\n";
}