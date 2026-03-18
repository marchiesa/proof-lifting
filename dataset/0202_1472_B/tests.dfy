// --- Specification: models the problem structure ---

function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

function Pow2(exp: nat): nat
  decreases exp
{
  if exp == 0 then 1 else 2 * Pow2(exp - 1)
}

function Bit(mask: nat, i: nat): bool
  decreases i
{
  if i == 0 then mask % 2 == 1
  else Bit(mask / 2, i - 1)
}

function AliceWeight(a: seq<int>, mask: nat): int
  decreases |a|
{
  if |a| == 0 then 0
  else AliceWeight(a[..|a|-1], mask) + (if Bit(mask, |a| - 1) then a[|a|-1] else 0)
}

function BobWeight(a: seq<int>, mask: nat): int
  decreases |a|
{
  if |a| == 0 then 0
  else BobWeight(a[..|a|-1], mask) + (if !Bit(mask, |a| - 1) then a[|a|-1] else 0)
}

predicate CanDivideFairly(a: seq<int>)
{
  exists mask: nat | 0 <= mask < Pow2(|a|) ::
    AliceWeight(a, mask) == BobWeight(a, mask)
}

// --- Method with specification ---

method FairDivision(a: seq<int>) returns (result: bool)
  requires forall i | 0 <= i < |a| :: a[i] == 1 || a[i] == 2
  ensures result == CanDivideFairly(a)
{
  var s := 0;
  var count1 := 0;
  var count2 := 0;
  var i := 0;
  while i < |a|
  {
    s := s + a[i];
    if a[i] == 1 {
      count1 := count1 + 1;
    }
    if a[i] == 2 {
      count2 := count2 + 1;
    }
    i := i + 1;
  }
  if s % 2 == 1 {
    return false;
  }
  if count2 % 2 == 1 && count1 == 0 {
    return false;
  }
  return true;
}

method Main()
{
  // ============================================================
  // SPEC POSITIVE TESTS (small inputs only, CanDivideFairly)
  // ============================================================

  // From test 2: [1,1] -> YES
  expect CanDivideFairly([1, 1]) == true, "spec positive 1";

  // From test 3: [1,2] -> NO
  expect CanDivideFairly([1, 2]) == false, "spec positive 2";

  // From test 5: [2,2,2] -> NO
  expect CanDivideFairly([2, 2, 2]) == false, "spec positive 3";

  // From test 7: [1] -> NO
  expect CanDivideFairly([1]) == false, "spec positive 4";

  // From test 8: [2] -> NO
  expect CanDivideFairly([2]) == false, "spec positive 5";

  // From test 1 sub-case: [2,1,2] -> NO (length 3)
  expect CanDivideFairly([2, 1, 2]) == false, "spec positive 6";

  // Scaled from test 9 ([1,1,1,1,2,2,2,2]->YES): [2,2] -> YES
  expect CanDivideFairly([2, 2]) == true, "spec positive 7";

  // Scaled from test 6 ([2,2,2,1,1,1]->NO, odd sum): [2,1] -> NO
  expect CanDivideFairly([2, 1]) == false, "spec positive 8";

  // ============================================================
  // SPEC NEGATIVE TESTS (small inputs, wrong output must be rejected)
  // ============================================================

  // Neg 2: [1,1] wrong=false (correct=true)
  expect (false != CanDivideFairly([1, 1])), "spec negative 1";

  // Neg 3: [1,2] wrong=true (correct=false)
  expect (true != CanDivideFairly([1, 2])), "spec negative 2";

  // Neg 5: [2,2,2] wrong=true (correct=false)
  expect (true != CanDivideFairly([2, 2, 2])), "spec negative 3";

  // Neg 7: [1] wrong=true (correct=false)
  expect (true != CanDivideFairly([1])), "spec negative 4";

  // Neg 8: [2] wrong=true (correct=false)
  expect (true != CanDivideFairly([2])), "spec negative 5";

  // Scaled neg 9 ([1,1,1,1,2,2,2,2] wrong=false): [2,2] wrong=false (correct=true)
  expect (false != CanDivideFairly([2, 2])), "spec negative 6";

  // Scaled neg 6 ([2,2,2,1,1,1] wrong=true): [2,1] wrong=true (correct=false)
  expect (true != CanDivideFairly([2, 1])), "spec negative 7";

  // Neg 4: [1,2,1,2] wrong=false (correct=true), length 4
  expect (false != CanDivideFairly([1, 2, 1, 2])), "spec negative 8";

  // ============================================================
  // IMPLEMENTATION TESTS (full-size inputs)
  // ============================================================

  // Test 1 sub-cases
  var r1 := FairDivision([1, 1]);
  expect r1 == true, "impl test 1 failed";

  var r2 := FairDivision([1, 2]);
  expect r2 == false, "impl test 2 failed";

  var r3 := FairDivision([1, 2, 1, 2]);
  expect r3 == true, "impl test 3 failed";

  var r4 := FairDivision([2, 2, 2]);
  expect r4 == false, "impl test 4 failed";

  var r5 := FairDivision([2, 1, 2]);
  expect r5 == false, "impl test 5 failed";

  // Test 6
  var r6 := FairDivision([2, 2, 2, 1, 1, 1]);
  expect r6 == false, "impl test 6 failed";

  // Test 7
  var r7 := FairDivision([1]);
  expect r7 == false, "impl test 7 failed";

  // Test 8
  var r8 := FairDivision([2]);
  expect r8 == false, "impl test 8 failed";

  // Test 9
  var r9 := FairDivision([1, 1, 1, 1, 2, 2, 2, 2]);
  expect r9 == true, "impl test 9 failed";

  // Test 10
  var r10 := FairDivision([1, 1, 1, 2, 2]);
  expect r10 == false, "impl test 10 failed";

  // Test 11
  var r11 := FairDivision([2, 2, 2, 2, 2, 1, 1, 1, 1, 1]);
  expect r11 == false, "impl test 11 failed";

  print "All tests passed\n";
}