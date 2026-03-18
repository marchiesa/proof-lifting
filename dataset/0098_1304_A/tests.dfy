predicate MeetAt(x: int, y: int, a: int, b: int, t: int)
{
  t >= 1 && x + t * a == y - t * b
}

method TwoRabbits(x: int, y: int, a: int, b: int) returns (t: int)
  requires x < y
  requires a >= 1
  requires b >= 1
  ensures t == -1 || t >= 1
  ensures t >= 1 ==> MeetAt(x, y, a, b, t)
  ensures t == -1 ==> forall t' | 1 <= t' <= y - x :: !MeetAt(x, y, a, b, t')
{
  var z := y - x;
  var c := a + b;
  if z % c != 0 {
    t := -1;
  } else {
    t := z / c;
  }
}

method Main()
{
  // ========== SPEC POSITIVE TESTS ==========
  // Test pair 1 (5 cases)
  expect MeetAt(0, 10, 2, 3, 2), "spec positive 1a";
  expect forall t' | 1 <= t' <= 10 :: !MeetAt(0, 10, 3, 3, t'), "spec positive 1b";
  expect MeetAt(900000000, 1000000000, 1, 9999999, 10), "spec positive 1c";
  expect forall t' | 1 <= t' <= 1 :: !MeetAt(1, 2, 1, 1, t'), "spec positive 1d";
  expect MeetAt(1, 3, 1, 1, 1), "spec positive 1e";

  // Test pair 2
  expect MeetAt(0, 10, 2, 3, 2), "spec positive 2";

  // Test pair 3
  expect forall t' | 1 <= t' <= 10 :: !MeetAt(0, 10, 3, 3, t'), "spec positive 3";

  // Test pair 4
  expect forall t' | 1 <= t' <= 1 :: !MeetAt(1, 2, 1, 1, t'), "spec positive 4";

  // Test pair 5
  expect MeetAt(1, 3, 1, 1, 1), "spec positive 5";

  // Test pair 6
  expect MeetAt(0, 50, 5, 5, 5), "spec positive 6";

  // Test pair 7
  expect MeetAt(0, 6, 1, 2, 2), "spec positive 7";

  // Test pair 8
  expect MeetAt(10, 20, 3, 7, 1), "spec positive 8";

  // Test pair 9 (3 cases)
  expect MeetAt(0, 4, 2, 2, 1), "spec positive 9a";
  expect MeetAt(5, 15, 1, 4, 2), "spec positive 9b";
  expect MeetAt(0, 7, 3, 4, 1), "spec positive 9c";

  // Test pair 10 (4 cases)
  expect forall t' | 1 <= t' <= 1 :: !MeetAt(0, 1, 1, 1, t'), "spec positive 10a";
  expect MeetAt(0, 2, 1, 1, 1), "spec positive 10b";
  expect MeetAt(0, 3, 1, 2, 1), "spec positive 10c";
  expect MeetAt(1, 5, 2, 2, 1), "spec positive 10d";

  // ========== SPEC NEGATIVE TESTS ==========
  // Negative 1: (0,10,2,3) wrong t=3 instead of 2
  expect !MeetAt(0, 10, 2, 3, 3), "spec negative 1";
  // Negative 2: (0,10,2,3) wrong t=3
  expect !MeetAt(0, 10, 2, 3, 3), "spec negative 2";
  // Negative 3: (0,10,3,3) wrong t=0 instead of -1
  expect !MeetAt(0, 10, 3, 3, 0), "spec negative 3";
  // Negative 4: (1,2,1,1) wrong t=0 instead of -1
  expect !MeetAt(1, 2, 1, 1, 0), "spec negative 4";
  // Negative 5: (1,3,1,1) wrong t=2 instead of 1
  expect !MeetAt(1, 3, 1, 1, 2), "spec negative 5";
  // Negative 6: (0,50,5,5) wrong t=6 instead of 5
  expect !MeetAt(0, 50, 5, 5, 6), "spec negative 6";
  // Negative 7: (0,6,1,2) wrong t=3 instead of 2
  expect !MeetAt(0, 6, 1, 2, 3), "spec negative 7";
  // Negative 8: (10,20,3,7) wrong t=2 instead of 1
  expect !MeetAt(10, 20, 3, 7, 2), "spec negative 8";
  // Negative 9: (0,4,2,2) wrong t=2 instead of 1
  expect !MeetAt(0, 4, 2, 2, 2), "spec negative 9";
  // Negative 10: (0,1,1,1) wrong t=0 instead of -1
  expect !MeetAt(0, 1, 1, 1, 0), "spec negative 10";

  // ========== IMPLEMENTATION TESTS ==========
  // Test pair 1
  var t1a := TwoRabbits(0, 10, 2, 3);
  expect t1a == 2, "impl test 1a";
  var t1b := TwoRabbits(0, 10, 3, 3);
  expect t1b == -1, "impl test 1b";
  var t1c := TwoRabbits(900000000, 1000000000, 1, 9999999);
  expect t1c == 10, "impl test 1c";
  var t1d := TwoRabbits(1, 2, 1, 1);
  expect t1d == -1, "impl test 1d";
  var t1e := TwoRabbits(1, 3, 1, 1);
  expect t1e == 1, "impl test 1e";

  // Test pair 2
  var t2 := TwoRabbits(0, 10, 2, 3);
  expect t2 == 2, "impl test 2";

  // Test pair 3
  var t3 := TwoRabbits(0, 10, 3, 3);
  expect t3 == -1, "impl test 3";

  // Test pair 4
  var t4 := TwoRabbits(1, 2, 1, 1);
  expect t4 == -1, "impl test 4";

  // Test pair 5
  var t5 := TwoRabbits(1, 3, 1, 1);
  expect t5 == 1, "impl test 5";

  // Test pair 6
  var t6 := TwoRabbits(0, 50, 5, 5);
  expect t6 == 5, "impl test 6";

  // Test pair 7
  var t7 := TwoRabbits(0, 6, 1, 2);
  expect t7 == 2, "impl test 7";

  // Test pair 8
  var t8 := TwoRabbits(10, 20, 3, 7);
  expect t8 == 1, "impl test 8";

  // Test pair 9
  var t9a := TwoRabbits(0, 4, 2, 2);
  expect t9a == 1, "impl test 9a";
  var t9b := TwoRabbits(5, 15, 1, 4);
  expect t9b == 2, "impl test 9b";
  var t9c := TwoRabbits(0, 7, 3, 4);
  expect t9c == 1, "impl test 9c";

  // Test pair 10
  var t10a := TwoRabbits(0, 1, 1, 1);
  expect t10a == -1, "impl test 10a";
  var t10b := TwoRabbits(0, 2, 1, 1);
  expect t10b == 1, "impl test 10b";
  var t10c := TwoRabbits(0, 3, 1, 2);
  expect t10c == 1, "impl test 10c";
  var t10d := TwoRabbits(1, 5, 2, 2);
  expect t10d == 1, "impl test 10d";

  print "All tests passed\n";
}