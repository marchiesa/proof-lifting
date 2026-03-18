function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0
  else Sum(a[..|a|-1]) + a[|a|-1]
}

function Product(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 1
  else Product(a[..|a|-1]) * a[|a|-1]
}

predicate CanDistribute(a: seq<int>, budget: nat)
  decreases |a|
{
  if |a| == 0 then
    budget == 0
  else
    exists d | 0 <= d <= budget ::
      a[|a|-1] + d != 0 &&
      CanDistribute(a[..|a|-1], budget - d)
}

predicate Feasible(a: seq<int>, budget: nat)
{
  Sum(a) + budget != 0 &&
  CanDistribute(a, budget)
}

method NonZero(a: seq<int>) returns (steps: int)
  requires |a| > 0
  ensures steps >= 0
  ensures Feasible(a, steps as nat)
  ensures forall k | 0 <= k < steps :: !Feasible(a, k as nat)
{
  var s := 0;
  var z := 0;
  var i := 0;
  while i < |a|
  {
    s := s + a[i];
    if a[i] == 0 {
      z := z + 1;
    }
    i := i + 1;
  }
  if s + z == 0 {
    return z + 1;
  } else {
    return z;
  }
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Verify Feasible(a, correct) and minimality using small equivalent inputs.

  // Spec positive 1: equiv Test 1.1 [2,-1,-1]->1 (s=0,z=0,s+z=0->z+1=1)
  expect Feasible([-1, 1], 1), "spec positive 1";
  expect !Feasible([-1, 1], 0), "spec positive 1 minimal";

  // Spec positive 2: equiv Test 1.2 [-1,0,0,1]->2 (s=0,z=2,s+z=2->z=2)
  expect Feasible([0, 0], 2), "spec positive 2";
  expect !Feasible([0, 0], 0), "spec positive 2 minimal k=0";
  expect !Feasible([0, 0], 1), "spec positive 2 minimal k=1";

  // Spec positive 3: equiv Test 1.3 [-1,2]->0 (s=1,z=0->z=0)
  expect Feasible([1, 2], 0), "spec positive 3";

  // Spec positive 4: equiv Test 1.4 [0,-2,1]->2 (s=-1,z=1,s+z=0->z+1=2)
  expect Feasible([0, -1], 2), "spec positive 4";
  expect !Feasible([0, -1], 0), "spec positive 4 minimal k=0";
  expect !Feasible([0, -1], 1), "spec positive 4 minimal k=1";

  // Spec positive 5: equiv Test 2 [0]->1 (s=0,z=1,s+z=1->z=1)
  expect Feasible([0], 1), "spec positive 5";
  expect !Feasible([0], 0), "spec positive 5 minimal";

  // Spec positive 6: equiv Test 3 (all positive, no zeros) -> [5]->0
  expect Feasible([5], 0), "spec positive 6";

  // Spec positive 7: equiv Tests 4,6,7 (sum=0, no zeros) -> [2,-2]->1
  expect Feasible([2, -2], 1), "spec positive 7";
  expect !Feasible([2, -2], 0), "spec positive 7 minimal";

  // ===== SPEC NEGATIVE TESTS =====
  // Verify the wrong output does NOT satisfy all ensures (Feasible + minimality).
  // Negate the conjunction: Feasible(a, wrong) && forall k<wrong: !Feasible(a,k).

  // Spec negative 1: equiv Neg 1 [2,-1,-1] wrong=2 -> [-1,1] wrong=2
  expect !(Feasible([-1, 1], 2) && !Feasible([-1, 1], 0) && !Feasible([-1, 1], 1)),
    "spec negative 1";

  // Spec negative 2: equiv Neg 2 [0] wrong=2 -> [0] wrong=2
  expect !(Feasible([0], 2) && !Feasible([0], 0) && !Feasible([0], 1)),
    "spec negative 2";

  // Spec negative 3: equiv Neg 3 (all 64s, wrong=1) -> [5] wrong=1
  expect !(Feasible([5], 1) && !Feasible([5], 0)),
    "spec negative 3";

  // Spec negative 4: equiv Neg 4 (alt 64/-64, wrong=2) -> [2,-2] wrong=2
  expect !(Feasible([2, -2], 2) && !Feasible([2, -2], 0) && !Feasible([2, -2], 1)),
    "spec negative 4";

  // Spec negative 5: equiv Neg 5 (positive sum, wrong=1) -> [1,2] wrong=1
  expect !(Feasible([1, 2], 1) && !Feasible([1, 2], 0)),
    "spec negative 5";

  // Spec negative 6: equiv Neg 6 (alt 2/-2, wrong=2) -> [3,-3] wrong=2
  expect !(Feasible([3, -3], 2) && !Feasible([3, -3], 0) && !Feasible([3, -3], 1)),
    "spec negative 6";

  // Spec negative 7: equiv Neg 7 (twos then negative, wrong=2) -> [1,-1] wrong=2
  expect !(Feasible([1, -1], 2) && !Feasible([1, -1], 0) && !Feasible([1, -1], 1)),
    "spec negative 7";

  // ===== IMPLEMENTATION TESTS =====

  var r1 := NonZero([2, -1, -1]);
  expect r1 == 1, "impl test 1.1 failed";

  var r2 := NonZero([-1, 0, 0, 1]);
  expect r2 == 2, "impl test 1.2 failed";

  var r3 := NonZero([-1, 2]);
  expect r3 == 0, "impl test 1.3 failed";

  var r4 := NonZero([0, -2, 1]);
  expect r4 == 2, "impl test 1.4 failed";

  var r5 := NonZero([0]);
  expect r5 == 1, "impl test 2 failed";

  var r6 := NonZero(seq(100, i => 64));
  expect r6 == 0, "impl test 3 failed";

  var r7 := NonZero(seq(100, i => if i % 2 == 0 then 64 else -64));
  expect r7 == 1, "impl test 4 failed";

  var r8 := NonZero([-95, -42, 85, 39, 3, 30, -80, 26, -28, 46, -55, -27, 13, 99, 3, 98, 18, 17, 57, -35, 8, -97, -8, 13, -5, 65, 6, 38, 42, -96, 55, -67, 98, -39, 94, 25, 18, -22, -57, -99, 22, 49, -34, -38, -8, -84, -10, 16, -35, 16, 91, 9, 98, -20, 31, 34, 86, -2, 23, 99, 31, 28, -1, -19, 42, 49, 14, 36, -33, 6, 97, 18, -27, 22, -22, 46, -58, -88, -36, -98, -59, 37, 3, 2]);
  expect r8 == 0, "impl test 5 failed";

  var r9 := NonZero(seq(64, i => if i % 2 == 0 then 2 else -2));
  expect r9 == 1, "impl test 6 failed";

  var r10 := NonZero(seq(49, i => 2) + [-98]);
  expect r10 == 1, "impl test 7 failed";

  print "All tests passed\n";
}