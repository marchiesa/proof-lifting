// === SPECIFICATION: Park Lighting ===

function NumEdges(n: int, m: int): int
  requires n >= 1 && m >= 1
{
  (n + 1) * m + n * (m + 1)
}

function Pow2(e: int): int
  requires e >= 0
  decreases e
{
  if e == 0 then 1 else 2 * Pow2(e - 1)
}

predicate BitSet(p: int, k: int)
  requires p >= 0 && k >= 0
  decreases k
{
  if k == 0 then p % 2 == 1
  else BitSet(p / 2, k - 1)
}

function CountOnes(p: int): int
  requires p >= 0
  decreases p
{
  if p == 0 then 0
  else (if p % 2 == 1 then 1 else 0) + CountOnes(p / 2)
}

predicate EdgeAdjacentToCell(n: int, m: int, e: int, r: int, c: int)
  requires n >= 1 && m >= 1
  requires 0 <= r < n && 0 <= c < m
  requires 0 <= e < NumEdges(n, m)
{
  e == r * m + c
  || e == (r + 1) * m + c
  || e == (n + 1) * m + r * (m + 1) + c
  || e == (n + 1) * m + r * (m + 1) + (c + 1)
}

predicate CellLit(n: int, m: int, p: int, r: int, c: int)
  requires n >= 1 && m >= 1
  requires 0 <= r < n && 0 <= c < m
  requires p >= 0
{
  exists e | 0 <= e < NumEdges(n, m) ::
    BitSet(p, e) && EdgeAdjacentToCell(n, m, e, r, c)
}

predicate AllCellsLit(n: int, m: int, p: int)
  requires n >= 1 && m >= 1
  requires p >= 0
{
  forall r, c | 0 <= r < n && 0 <= c < m ::
    CellLit(n, m, p, r, c)
}

predicate IsMinLanternCount(n: int, m: int, count: int)
  requires n >= 1 && m >= 1
{
  var E := NumEdges(n, m);
  (exists p | 0 <= p < Pow2(E) ::
     AllCellsLit(n, m, p) && CountOnes(p) == count)
  &&
  (forall p | 0 <= p < Pow2(E) ::
     AllCellsLit(n, m, p) ==> CountOnes(p) >= count)
}

// === IMPLEMENTATION ===

method ParkLighting(n: int, m: int) returns (lanterns: int)
  requires n >= 1 && m >= 1
  ensures IsMinLanternCount(n, m, lanterns)
{
  var x := n * m;
  x := x + 1;
  lanterns := x / 2;
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // Small inputs only (bounded quantifiers over Pow2(NumEdges) must be feasible)

  // From Test 3: (1,1) -> 1
  expect IsMinLanternCount(1, 1, 1), "spec positive 1";
  // From Test 4: (1,2) -> 1
  expect IsMinLanternCount(1, 2, 1), "spec positive 2";
  // From Test 12a: (2,1) -> 1
  expect IsMinLanternCount(2, 1, 1), "spec positive 3";
  // From Test 1b: (1,3) -> 2
  expect IsMinLanternCount(1, 3, 2), "spec positive 4";
  // From Test 1c / 7b: (2,2) -> 2
  expect IsMinLanternCount(2, 2, 2), "spec positive 5";

  // === SPEC NEGATIVE TESTS ===
  // Wrong outputs from negative test pairs, small inputs only

  // From Neg 1: (1,1) wrong=2, correct=1
  expect !IsMinLanternCount(1, 1, 2), "spec negative 1";
  // From Neg 3: (1,1) wrong=2, correct=1
  expect !IsMinLanternCount(1, 1, 2), "spec negative 3";
  // From Neg 4: (1,2) wrong=2, correct=1
  expect !IsMinLanternCount(1, 2, 2), "spec negative 4";
  // From Neg 7: (1,1) wrong=2, correct=1
  expect !IsMinLanternCount(1, 1, 2), "spec negative 7";
  // From Neg 8: (1,3) wrong=3, correct=2
  expect !IsMinLanternCount(1, 3, 3), "spec negative 8";

  // === IMPLEMENTATION TESTS ===

  // Test 1
  var r1 := ParkLighting(1, 1);
  expect r1 == 1, "impl test 1a failed";
  var r2 := ParkLighting(1, 3);
  expect r2 == 2, "impl test 1b failed";
  var r3 := ParkLighting(2, 2);
  expect r3 == 2, "impl test 1c failed";
  var r4 := ParkLighting(3, 3);
  expect r4 == 5, "impl test 1d failed";
  var r5 := ParkLighting(5, 3);
  expect r5 == 8, "impl test 1e failed";

  // Test 2
  var r6 := ParkLighting(1329, 2007);
  expect r6 == 1333652, "impl test 2a failed";
  var r7 := ParkLighting(179, 57);
  expect r7 == 5102, "impl test 2b failed";

  // Test 3
  var r8 := ParkLighting(1, 1);
  expect r8 == 1, "impl test 3 failed";

  // Test 4
  var r9 := ParkLighting(1, 2);
  expect r9 == 1, "impl test 4 failed";

  // Test 5
  var r10 := ParkLighting(2, 3);
  expect r10 == 3, "impl test 5 failed";

  // Test 6
  var r11 := ParkLighting(5, 5);
  expect r11 == 13, "impl test 6 failed";

  // Test 7
  var r12 := ParkLighting(1, 1);
  expect r12 == 1, "impl test 7a failed";
  var r13 := ParkLighting(2, 2);
  expect r13 == 2, "impl test 7b failed";
  var r14 := ParkLighting(3, 3);
  expect r14 == 5, "impl test 7c failed";

  // Test 8
  var r15 := ParkLighting(1, 3);
  expect r15 == 2, "impl test 8a failed";
  var r16 := ParkLighting(2, 2);
  expect r16 == 2, "impl test 8b failed";
  var r17 := ParkLighting(3, 3);
  expect r17 == 5, "impl test 8c failed";
  var r18 := ParkLighting(5, 3);
  expect r18 == 8, "impl test 8d failed";
  var r19 := ParkLighting(4, 4);
  expect r19 == 8, "impl test 8e failed";

  // Test 9
  var r20 := ParkLighting(10, 10);
  expect r20 == 50, "impl test 9 failed";

  // Test 10
  var r21 := ParkLighting(1, 50);
  expect r21 == 25, "impl test 10a failed";
  var r22 := ParkLighting(50, 1);
  expect r22 == 25, "impl test 10b failed";
  var r23 := ParkLighting(7, 9);
  expect r23 == 32, "impl test 10c failed";
  var r24 := ParkLighting(3, 6);
  expect r24 == 9, "impl test 10d failed";

  // Test 11
  var r25 := ParkLighting(1, 1);
  expect r25 == 1, "impl test 11a failed";
  var r26 := ParkLighting(50, 50);
  expect r26 == 1250, "impl test 11b failed";

  // Test 12
  var r27 := ParkLighting(2, 1);
  expect r27 == 1, "impl test 12a failed";
  var r28 := ParkLighting(1, 4);
  expect r28 == 2, "impl test 12b failed";
  var r29 := ParkLighting(3, 5);
  expect r29 == 8, "impl test 12c failed";
  var r30 := ParkLighting(4, 2);
  expect r30 == 4, "impl test 12d failed";
  var r31 := ParkLighting(6, 7);
  expect r31 == 21, "impl test 12e failed";
  var r32 := ParkLighting(8, 3);
  expect r32 == 12, "impl test 12f failed";

  print "All tests passed\n";
}