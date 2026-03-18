predicate IsTriangle(x: int, y: int, z: int)
{
  x + y > z && x + z > y && y + z > x
}

predicate CanFormTriangleWithKMinutes(a: int, b: int, c: int, k: int)
{
  k >= 0 &&
  exists da | 0 <= da <= k ::
    exists db | 0 <= db <= k - da ::
      IsTriangle(a + da, b + db, c + (k - da - db))
}

predicate IsMinimalMinutes(a: int, b: int, c: int, minutes: int)
{
  CanFormTriangleWithKMinutes(a, b, c, minutes) &&
  forall k | 0 <= k < minutes :: !CanFormTriangleWithKMinutes(a, b, c, k)
}

method MakeTriangle(a: int, b: int, c: int) returns (minutes: int)
  requires a >= 1 && b >= 1 && c >= 1
  ensures minutes >= 0
  ensures IsMinimalMinutes(a, b, c, minutes)
{
  var m := a;
  if b > m { m := b; }
  if c > m { m := c; }
  var diff := m - a - b - c + m + 1;
  if diff < 0 { minutes := 0; } else { minutes := diff; }
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // IsMinimalMinutes(a, b, c, correct) should be true
  // Using small inputs / small minutes to keep bounded quantifiers fast

  // 1: (3,4,5) -> 0
  expect IsMinimalMinutes(3, 4, 5, 0), "spec positive 1";
  // 2: (2,5,3) -> 1
  expect IsMinimalMinutes(2, 5, 3, 1), "spec positive 2";
  // 3: scaled from (100,10,10)->81 to (5,1,1)->4
  expect IsMinimalMinutes(5, 1, 1, 4), "spec positive 3";
  // 4: (1,1,1) -> 0
  expect IsMinimalMinutes(1, 1, 1, 0), "spec positive 4";
  // 5: (100,100,100) -> 0  [minutes=0, trivially fast]
  expect IsMinimalMinutes(100, 100, 100, 0), "spec positive 5";
  // 6: scaled from (100,1,1)->99 to (4,1,1)->3
  expect IsMinimalMinutes(4, 1, 1, 3), "spec positive 6";
  // 7: scaled from (12,34,56)->11 to (1,3,5)->2
  expect IsMinimalMinutes(1, 3, 5, 2), "spec positive 7";
  // 8: (68,1,67) -> 1  [minutes=1, fast]
  expect IsMinimalMinutes(68, 1, 67, 1), "spec positive 8";
  // 9: (100,100,1) -> 0  [minutes=0, fast]
  expect IsMinimalMinutes(100, 100, 1, 0), "spec positive 9";
  // 10: (100,1,99) -> 1  [minutes=1, fast]
  expect IsMinimalMinutes(100, 1, 99, 1), "spec positive 10";

  // === SPEC NEGATIVE TESTS ===
  // IsMinimalMinutes(a, b, c, wrong) should be false

  // 1: (3,4,5), wrong=1 (correct=0)
  expect !IsMinimalMinutes(3, 4, 5, 1), "spec negative 1";
  // 2: (2,5,3), wrong=2 (correct=1)
  expect !IsMinimalMinutes(2, 5, 3, 2), "spec negative 2";
  // 3: scaled from (100,10,10) wrong=82 to (5,1,1) wrong=5
  expect !IsMinimalMinutes(5, 1, 1, 5), "spec negative 3";
  // 4: (1,1,1), wrong=1 (correct=0)
  expect !IsMinimalMinutes(1, 1, 1, 1), "spec negative 4";
  // 5: (100,100,100), wrong=1 (correct=0)
  expect !IsMinimalMinutes(100, 100, 100, 1), "spec negative 5";
  // 6: scaled from (100,1,1) wrong=100 to (4,1,1) wrong=4
  expect !IsMinimalMinutes(4, 1, 1, 4), "spec negative 6";
  // 7: scaled from (12,34,56) wrong=12 to (1,3,5) wrong=3
  expect !IsMinimalMinutes(1, 3, 5, 3), "spec negative 7";
  // 8: (68,1,67), wrong=2 (correct=1)
  expect !IsMinimalMinutes(68, 1, 67, 2), "spec negative 8";
  // 9: (100,100,1), wrong=1 (correct=0)
  expect !IsMinimalMinutes(100, 100, 1, 1), "spec negative 9";
  // 10: (100,1,99), wrong=2 (correct=1)
  expect !IsMinimalMinutes(100, 1, 99, 2), "spec negative 10";

  // === IMPLEMENTATION TESTS ===
  var r1 := MakeTriangle(3, 4, 5);
  expect r1 == 0, "impl test 1 failed";

  var r2 := MakeTriangle(2, 5, 3);
  expect r2 == 1, "impl test 2 failed";

  var r3 := MakeTriangle(100, 10, 10);
  expect r3 == 81, "impl test 3 failed";

  var r4 := MakeTriangle(1, 1, 1);
  expect r4 == 0, "impl test 4 failed";

  var r5 := MakeTriangle(100, 100, 100);
  expect r5 == 0, "impl test 5 failed";

  var r6 := MakeTriangle(100, 1, 1);
  expect r6 == 99, "impl test 6 failed";

  var r7 := MakeTriangle(12, 34, 56);
  expect r7 == 11, "impl test 7 failed";

  var r8 := MakeTriangle(68, 1, 67);
  expect r8 == 1, "impl test 8 failed";

  var r9 := MakeTriangle(100, 100, 1);
  expect r9 == 0, "impl test 9 failed";

  var r10 := MakeTriangle(100, 1, 99);
  expect r10 == 1, "impl test 10 failed";

  print "All tests passed\n";
}