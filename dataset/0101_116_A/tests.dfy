function Sum(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else Sum(s[..|s|-1]) + s[|s|-1]
}

function Occupancy(a: seq<int>, b: seq<int>): int
  requires |a| == |b|
{
  Sum(b) - Sum(a)
}

predicate IsValidCapacity(c: int, n: int, a: seq<int>, b: seq<int>)
  requires 0 <= n <= |a| && n <= |b|
{
  c >= 0 &&
  forall k | 1 <= k <= n :: Occupancy(a[..k], b[..k]) <= c
}

predicate IsMinimumCapacity(c: int, n: int, a: seq<int>, b: seq<int>)
  requires 0 <= n <= |a| && n <= |b|
{
  IsValidCapacity(c, n, a, b) &&
  forall c' | 0 <= c' < c :: !IsValidCapacity(c', n, a, b)
}

method Tram(n: int, a: seq<int>, b: seq<int>) returns (capacity: int)
  requires 0 <= n <= |a| && n <= |b|
  ensures IsMinimumCapacity(capacity, n, a, b)
{
  var current := 0;
  capacity := 0;
  var i := 0;
  while i < n
  {
    current := current - a[i] + b[i];
    if current > capacity {
      capacity := current;
    }
    i := i + 1;
  }
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // IsMinimumCapacity with correct output on small inputs

  // Spec pos 1 (from Test 4): n=3, a=[0,1,1], b=[1,1,0], cap=1
  expect IsMinimumCapacity(1, 3, [0,1,1], [1,1,0]), "spec positive 1";

  // Spec pos 2 (from Test 6): n=3, a=[0,0,0], b=[0,0,0], cap=0
  expect IsMinimumCapacity(0, 3, [0,0,0], [0,0,0]), "spec positive 2";

  // Spec pos 3 (from Test 5 scaled): n=2, a=[0,0], b=[1,1], cap=2
  expect IsMinimumCapacity(2, 2, [0,0], [1,1]), "spec positive 3";

  // Spec pos 4 (from Test 9 scaled): n=3, a=[0,0,1], b=[0,1,0], cap=1
  expect IsMinimumCapacity(1, 3, [0,0,1], [0,1,0]), "spec positive 4";

  // Spec pos 5 (from Test 11 scaled): n=3, a=[0,1,2], b=[1,2,0], cap=2
  expect IsMinimumCapacity(2, 3, [0,1,2], [1,2,0]), "spec positive 5";

  // Spec pos 6 (from Test 1 scaled): n=2, a=[0,2], b=[3,2], cap=3
  expect IsMinimumCapacity(3, 2, [0,2], [3,2]), "spec positive 6";

  // Spec pos 7 (from Test 7 scaled): n=1, a=[0], b=[5], cap=5
  expect IsMinimumCapacity(5, 1, [0], [5]), "spec positive 7";

  // === SPEC NEGATIVE TESTS ===
  // IsMinimumCapacity with wrong output (correct+1) on small inputs

  // Spec neg 1: wrong=2 (correct=1)
  expect !IsMinimumCapacity(2, 3, [0,1,1], [1,1,0]), "spec negative 1";

  // Spec neg 2: wrong=1 (correct=0)
  expect !IsMinimumCapacity(1, 3, [0,0,0], [0,0,0]), "spec negative 2";

  // Spec neg 3: wrong=3 (correct=2)
  expect !IsMinimumCapacity(3, 2, [0,0], [1,1]), "spec negative 3";

  // Spec neg 4: wrong=2 (correct=1)
  expect !IsMinimumCapacity(2, 3, [0,0,1], [0,1,0]), "spec negative 4";

  // Spec neg 5: wrong=3 (correct=2)
  expect !IsMinimumCapacity(3, 3, [0,1,2], [1,2,0]), "spec negative 5";

  // Spec neg 6: wrong=4 (correct=3)
  expect !IsMinimumCapacity(4, 2, [0,2], [3,2]), "spec negative 6";

  // Spec neg 7: wrong=6 (correct=5)
  expect !IsMinimumCapacity(6, 1, [0], [5]), "spec negative 7";

  // === IMPLEMENTATION TESTS ===

  var r1 := Tram(4, [0,2,4,4], [3,5,2,0]);
  expect r1 == 6, "impl test 1 failed";

  var r2 := Tram(5, [0,4,6,5,4], [4,6,5,4,0]);
  expect r2 == 6, "impl test 2 failed";

  var r3 := Tram(10, [0,1,10,5,0,3,8,0,10,9], [5,7,8,3,5,3,8,6,1,0]);
  expect r3 == 18, "impl test 3 failed";

  var r4 := Tram(3, [0,1,1], [1,1,0]);
  expect r4 == 1, "impl test 4 failed";

  var r5 := Tram(4, [0,0,1,1], [1,1,0,0]);
  expect r5 == 2, "impl test 5 failed";

  var r6 := Tram(3, [0,0,0], [0,0,0]);
  expect r6 == 0, "impl test 6 failed";

  var r7 := Tram(3, [0,1000,1000], [1000,1000,0]);
  expect r7 == 1000, "impl test 7 failed";

  var r8 := Tram(5, [0,73,189,766,0], [73,189,766,0,0]);
  expect r8 == 766, "impl test 8 failed";

  var r9 := Tram(5, [0,0,0,0,1], [0,0,0,1,0]);
  expect r9 == 1, "impl test 9 failed";

  var r10 := Tram(5, [0,917,904,1000,11], [917,923,992,0,0]);
  expect r10 == 1011, "impl test 10 failed";

  var r11 := Tram(5, [0,1,2,1,2], [1,2,1,2,0]);
  expect r11 == 2, "impl test 11 failed";

  var r12 := Tram(5, [0,0,0,0,0], [0,0,0,0,0]);
  expect r12 == 0, "impl test 12 failed";

  var r13 := Tram(20, [0,2,2,5,2,6,2,0,7,8,10,2,6,1,0,8,6,6,1,3], [7,1,2,7,6,10,4,4,4,0,6,1,1,7,3,7,3,3,1,0]);
  expect r13 == 22, "impl test 13 failed";

  var r14 := Tram(5, [0,1000,1000,1000,1000], [1000,1000,1000,1000,0]);
  expect r14 == 1000, "impl test 14 failed";

  var r15 := Tram(10, [0,258,389,249,196,478,994,1000,769,0], [592,598,203,836,635,482,987,0,0,0]);
  expect r15 == 1776, "impl test 15 failed";

  var r16 := Tram(10, [0,1,0,0,0,0,1,0,1,1], [1,0,0,0,0,1,1,1,0,0]);
  expect r16 == 2, "impl test 16 failed";

  var r17 := Tram(10, [0,926,938,931,937,983,908,997,945,988], [926,938,931,964,989,936,949,932,988,0]);
  expect r17 == 1016, "impl test 17 failed";

  var r18 := Tram(10, [0,1,1,2,2,2,1,1,2,2], [1,2,2,2,2,2,1,1,1,0]);
  expect r18 == 3, "impl test 18 failed";

  var r19 := Tram(10, [0,0,0,0,0,0,0,0,0,0], [0,0,0,0,0,0,0,0,0,0]);
  expect r19 == 0, "impl test 19 failed";

  var r20 := Tram(10, [0,1000,1000,1000,1000,1000,1000,1000,1000,1000], [1000,1000,1000,1000,1000,1000,1000,1000,1000,0]);
  expect r20 == 1000, "impl test 20 failed";

  print "All tests passed\n";
}