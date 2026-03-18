// --- Specification functions ---

function Factorial(n: nat): nat
  decreases n
{
  if n == 0 then 1 else n * Factorial(n - 1)
}

function Iota(n: nat): seq<int>
  decreases n
{
  if n == 0 then [] else Iota(n - 1) + [n - 1]
}

function RemoveAt(s: seq<int>, idx: nat): seq<int>
  requires idx < |s|
{
  s[..idx] + s[idx + 1..]
}

function DecodePerm(k: nat, available: seq<int>): seq<int>
  decreases |available|
{
  if |available| == 0 then []
  else
    var idx := k % |available|;
    [available[idx]] + DecodePerm(k / |available|, RemoveAt(available, idx))
}

function PermFromIndex(k: nat, n: nat): seq<int>
{
  DecodePerm(k, Iota(n))
}

function ApplyPerm(a: seq<int>, perm: seq<int>): seq<int>
  requires forall i | 0 <= i < |perm| :: 0 <= perm[i] < |a|
  decreases |perm|
{
  if |perm| == 0 then []
  else [a[perm[0]]] + ApplyPerm(a, perm[1..])
}

function WeightedSum(a: seq<int>, pos: nat): real
  requires pos >= 1
  decreases |a|
{
  if |a| == 0 then 0.0
  else (a[0] as real) / (pos as real) + WeightedSum(a[1..], pos + 1)
}

function DoubleSumFrom(a: seq<int>, pos: nat): real
  requires pos >= 1
  decreases |a|
{
  if |a| == 0 then 0.0
  else WeightedSum(a, pos) + DoubleSumFrom(a[1..], pos + 1)
}

function DoubleSum(a: seq<int>): real
{
  DoubleSumFrom(a, 1)
}

predicate HasReorderingAt(a: seq<int>, k: nat, m: int)
{
  k < Factorial(|a|) &&
  var perm := PermFromIndex(k, |a|);
  |perm| == |a| &&
  (forall i | 0 <= i < |perm| :: 0 <= perm[i] < |a|) &&
  DoubleSum(ApplyPerm(a, perm)) == m as real
}

predicate CanReorderToSum(a: seq<int>, m: int)
{
  exists k: nat | k < Factorial(|a|) :: HasReorderingAt(a, k, m)
}

// --- Method with specification ---

method Reorder(a: seq<int>, m: int) returns (result: bool)
  ensures result == CanReorderToSum(a, m)
{
  var s := 0;
  for i := 0 to |a| {
    s := s + a[i];
  }
  result := m == s;
}

method Main()
{
  var r: bool;

  // ===== SPEC POSITIVE TESTS =====
  // Top-level ensures predicate with correct outputs (small inputs, len 1-3)

  // Test 1a: a=[2,5,1], m=8 → true
  expect CanReorderToSum([2, 5, 1], 8) == true, "spec positive 1";

  // Test 2: a=[2,4], m=2 → false
  expect CanReorderToSum([2, 4], 2) == false, "spec positive 2";

  // Test 3: a=[3,6], m=3 → false
  expect CanReorderToSum([3, 6], 3) == false, "spec positive 3";

  // Test 4: a=[0,0,0], m=0 → true
  expect CanReorderToSum([0, 0, 0], 0) == true, "spec positive 4";

  // Test 5: a=[2,2,2], m=2 → false
  expect CanReorderToSum([2, 2, 2], 2) == false, "spec positive 5";

  // Test 6: a=[1,1,1], m=1 → false
  expect CanReorderToSum([1, 1, 1], 1) == false, "spec positive 6";

  // Test 8: a=[0,0,0], m=3 → false
  expect CanReorderToSum([0, 0, 0], 3) == false, "spec positive 7";

  // Test 9: a=[2], m=1 → false
  expect CanReorderToSum([2], 1) == false, "spec positive 8";

  // Test 10: a=[2,2,2], m=3 → false
  expect CanReorderToSum([2, 2, 2], 3) == false, "spec positive 9";

  // ===== SPEC NEGATIVE TESTS =====
  // Top-level ensures predicate rejects wrong outputs (small inputs, len 1-3)

  // Neg 2: a=[2,4], m=2, wrong=true (correct=false)
  expect !CanReorderToSum([2, 4], 2), "spec negative 2";

  // Neg 3: a=[3,6], m=3, wrong=true (correct=false)
  expect !CanReorderToSum([3, 6], 3), "spec negative 3";

  // Neg 4: a=[0,0,0], m=0, wrong=false (correct=true)
  expect CanReorderToSum([0, 0, 0], 0), "spec negative 4";

  // Neg 5: a=[2,2,2], m=2, wrong=true (correct=false)
  expect !CanReorderToSum([2, 2, 2], 2), "spec negative 5";

  // Neg 6: a=[1,1,1], m=1, wrong=true (correct=false)
  expect !CanReorderToSum([1, 1, 1], 1), "spec negative 6";

  // Neg 8: a=[0,0,0], m=3, wrong=true (correct=false)
  expect !CanReorderToSum([0, 0, 0], 3), "spec negative 8";

  // Neg 9: a=[2], m=1, wrong=true (correct=false)
  expect !CanReorderToSum([2], 1), "spec negative 9";

  // Neg 10: a=[2,2,2], m=3, wrong=true (correct=false)
  expect !CanReorderToSum([2, 2, 2], 3), "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====

  // Test 1, case 1: a=[2,5,1], m=8 → true
  r := Reorder([2, 5, 1], 8);
  expect r == true, "impl test 1.1 failed";

  // Test 1, case 2: a=[0,1,2,3], m=4 → false
  r := Reorder([0, 1, 2, 3], 4);
  expect r == false, "impl test 1.2 failed";

  // Test 2: a=[2,4], m=2 → false
  r := Reorder([2, 4], 2);
  expect r == false, "impl test 2 failed";

  // Test 3: a=[3,6], m=3 → false
  r := Reorder([3, 6], 3);
  expect r == false, "impl test 3 failed";

  // Test 4: a=[0,0,0], m=0 → true
  r := Reorder([0, 0, 0], 0);
  expect r == true, "impl test 4 failed";

  // Test 5: a=[2,2,2], m=2 → false
  r := Reorder([2, 2, 2], 2);
  expect r == false, "impl test 5 failed";

  // Test 6: a=[1,1,1], m=1 → false
  r := Reorder([1, 1, 1], 1);
  expect r == false, "impl test 6 failed";

  // Test 7, case 1: a=[5,5,5,5], m=5 → false
  r := Reorder([5, 5, 5, 5], 5);
  expect r == false, "impl test 7.1 failed";

  // Test 7, case 2: a=[3,3,3,3,3,3], m=3 → false
  r := Reorder([3, 3, 3, 3, 3, 3], 3);
  expect r == false, "impl test 7.2 failed";

  // Test 8: a=[0,0,0], m=3 → false
  r := Reorder([0, 0, 0], 3);
  expect r == false, "impl test 8 failed";

  // Test 9: a=[2], m=1 → false
  r := Reorder([2], 1);
  expect r == false, "impl test 9 failed";

  // Test 10: a=[2,2,2], m=3 → false
  r := Reorder([2, 2, 2], 3);
  expect r == false, "impl test 10 failed";

  // Test 11: a=[10,13,9], m=8 → false
  r := Reorder([10, 13, 9], 8);
  expect r == false, "impl test 11 failed";

  // Test 12: a=[1], m=0 → false
  r := Reorder([1], 0);
  expect r == false, "impl test 12 failed";

  // Test 13: a=[16,0,0], m=8 → false
  r := Reorder([16, 0, 0], 8);
  expect r == false, "impl test 13 failed";

  // Test 14: a=[88,9,9,9,9,9], m=1 → false
  r := Reorder([88, 9, 9, 9, 9, 9], 1);
  expect r == false, "impl test 14 failed";

  // Test 15: a=[0], m=1 → false
  r := Reorder([0], 1);
  expect r == false, "impl test 15 failed";

  // Test 16: a=[4], m=2 → false
  r := Reorder([4], 2);
  expect r == false, "impl test 16 failed";

  // Test 17: a=[2,4,10], m=8 → false
  r := Reorder([2, 4, 10], 8);
  expect r == false, "impl test 17 failed";

  // Test 18: a=[5,10,15], m=5 → false
  r := Reorder([5, 10, 15], 5);
  expect r == false, "impl test 18 failed";

  // Test 19: a=[0,0,0], m=2 → false
  r := Reorder([0, 0, 0], 2);
  expect r == false, "impl test 19 failed";

  // Test 20: a=[15,8,1], m=8 → false
  r := Reorder([15, 8, 1], 8);
  expect r == false, "impl test 20 failed";

  print "All tests passed\n";
}