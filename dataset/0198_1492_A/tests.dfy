predicate SwimmerAtLeft(time: int, period: int)
  requires period > 0
  requires time >= 0
{
  time % period == 0
}

predicate SomeSwimmerAtLeft(time: int, a: int, b: int, c: int)
  requires a > 0 && b > 0 && c > 0
  requires time >= 0
{
  SwimmerAtLeft(time, a) || SwimmerAtLeft(time, b) || SwimmerAtLeft(time, c)
}

predicate IsMinimumWait(p: int, a: int, b: int, c: int, wait: int)
  requires p >= 1 && a > 0 && b > 0 && c > 0
{
  wait >= 0 &&
  SomeSwimmerAtLeft(p + wait, a, b, c) &&
  forall w | 0 <= w < wait :: !SomeSwimmerAtLeft(p + w, a, b, c)
}

method ThreeSwimmers(p: int, a: int, b: int, c: int) returns (wait: int)
  requires p >= 1 && a > 0 && b > 0 && c > 0
  ensures IsMinimumWait(p, a, b, c, wait)
{
  var wa := (a - p % a) % a;
  var wb := (b - p % b) % b;
  var wc := (c - p % c) % c;
  wait := wa;
  if wb < wait { wait := wb; }
  if wc < wait { wait := wc; }
}

method Main()
{
  var result: int;

  // ===== SPEC POSITIVE TESTS =====
  expect IsMinimumWait(2, 1, 1, 1, 0), "spec positive 1";
  expect IsMinimumWait(4, 2, 2, 2, 0), "spec positive 2";
  expect IsMinimumWait(1, 2, 3, 4, 1), "spec positive 3";
  expect IsMinimumWait(6, 2, 2, 2, 0), "spec positive 4";
  expect IsMinimumWait(8, 2, 3, 5, 0), "spec positive 5";
  expect IsMinimumWait(9, 5, 4, 8, 1), "spec positive 6";
  expect IsMinimumWait(10, 5, 7, 6, 0), "spec positive 7";
  expect IsMinimumWait(10, 2, 5, 10, 0), "spec positive 8";
  expect IsMinimumWait(2, 6, 10, 9, 4), "spec positive 9";
  expect IsMinimumWait(10, 9, 9, 9, 8), "spec positive 10";
  expect IsMinimumWait(12, 6, 6, 6, 0), "spec positive 11";
  expect IsMinimumWait(6, 3, 1000, 2000, 0), "spec positive 12";
  expect IsMinimumWait(20, 2, 5, 10, 0), "spec positive 13";
  expect IsMinimumWait(3, 1, 1, 1, 0), "spec positive 14";
  expect IsMinimumWait(10, 2, 3, 4, 0), "spec positive 15";
  expect IsMinimumWait(10, 2, 2, 2, 0), "spec positive 16";
  expect IsMinimumWait(4, 2, 100, 200, 0), "spec positive 17";
  expect IsMinimumWait(20, 10, 10, 10, 0), "spec positive 18";
  expect IsMinimumWait(8, 4, 4, 4, 0), "spec positive 19";
  expect IsMinimumWait(10, 5, 3, 4, 0), "spec positive 20";
  expect IsMinimumWait(100, 10, 11, 12, 0), "spec positive 21";
  expect IsMinimumWait(10, 2, 1000, 1000, 0), "spec positive 22";
  expect IsMinimumWait(1000000000000000000, 10, 7, 59465946, 0), "spec positive 23";
  expect IsMinimumWait(1000000000000000000, 1000000000000000000, 1000000000000000000, 1000000000000000000, 0), "spec positive 24";

  // ===== SPEC NEGATIVE TESTS =====
  expect !IsMinimumWait(9, 5, 4, 8, 2), "spec negative 1";       // correct=1, wrong=2
  expect !IsMinimumWait(1, 2, 3, 4, 2), "spec negative 2";       // correct=1, wrong=2
  expect !IsMinimumWait(2, 1, 1, 1, 1), "spec negative 3";       // correct=0, wrong=1
  expect !IsMinimumWait(4, 2, 2, 2, 1), "spec negative 4";       // correct=0, wrong=1
  expect !IsMinimumWait(12, 6, 6, 6, 1), "spec negative 5";      // correct=0, wrong=1
  expect !IsMinimumWait(10, 5, 7, 6, 1), "spec negative 6";      // correct=0, wrong=1
  expect !IsMinimumWait(20, 2, 5, 10, 1), "spec negative 7";     // correct=0, wrong=1
  expect !IsMinimumWait(6, 2, 2, 2, 1), "spec negative 8";       // correct=0, wrong=1
  expect !IsMinimumWait(6, 3, 1000, 2000, 1), "spec negative 9"; // correct=0, wrong=1
  expect !IsMinimumWait(8, 2, 3, 5, 1), "spec negative 10";      // correct=0, wrong=1

  // ===== IMPLEMENTATION TESTS =====
  result := ThreeSwimmers(9, 5, 4, 8);
  expect result == 1, "impl test 1.1 failed";
  result := ThreeSwimmers(2, 6, 10, 9);
  expect result == 4, "impl test 1.2 failed";
  result := ThreeSwimmers(10, 2, 5, 10);
  expect result == 0, "impl test 1.3 failed";
  result := ThreeSwimmers(10, 9, 9, 9);
  expect result == 8, "impl test 1.4 failed";

  result := ThreeSwimmers(1, 2, 3, 4);
  expect result == 1, "impl test 2.1 failed";
  result := ThreeSwimmers(1000000000000000000, 1000000000000000000, 1000000000000000000, 1000000000000000000);
  expect result == 0, "impl test 2.2 failed";

  result := ThreeSwimmers(2, 1, 1, 1);
  expect result == 0, "impl test 3 failed";
  result := ThreeSwimmers(4, 2, 2, 2);
  expect result == 0, "impl test 4 failed";
  result := ThreeSwimmers(12, 6, 6, 6);
  expect result == 0, "impl test 5 failed";
  result := ThreeSwimmers(10, 5, 7, 6);
  expect result == 0, "impl test 6 failed";
  result := ThreeSwimmers(20, 2, 5, 10);
  expect result == 0, "impl test 7 failed";
  result := ThreeSwimmers(6, 2, 2, 2);
  expect result == 0, "impl test 8 failed";

  result := ThreeSwimmers(6, 3, 1000, 2000);
  expect result == 0, "impl test 9.1 failed";
  result := ThreeSwimmers(9, 5, 4, 8);
  expect result == 1, "impl test 9.2 failed";
  result := ThreeSwimmers(2, 6, 10, 9);
  expect result == 4, "impl test 9.3 failed";
  result := ThreeSwimmers(10, 2, 5, 10);
  expect result == 0, "impl test 9.4 failed";
  result := ThreeSwimmers(10, 9, 9, 9);
  expect result == 8, "impl test 9.5 failed";

  result := ThreeSwimmers(8, 2, 3, 5);
  expect result == 0, "impl test 10 failed";
  result := ThreeSwimmers(20, 10, 10, 10);
  expect result == 0, "impl test 11 failed";
  result := ThreeSwimmers(8, 4, 4, 4);
  expect result == 0, "impl test 12 failed";
  result := ThreeSwimmers(100, 10, 11, 12);
  expect result == 0, "impl test 13 failed";
  result := ThreeSwimmers(10, 5, 3, 4);
  expect result == 0, "impl test 14 failed";
  result := ThreeSwimmers(10, 2, 1000, 1000);
  expect result == 0, "impl test 15 failed";
  result := ThreeSwimmers(3, 1, 1, 1);
  expect result == 0, "impl test 16 failed";
  result := ThreeSwimmers(10, 2, 3, 4);
  expect result == 0, "impl test 17 failed";
  result := ThreeSwimmers(10, 2, 2, 2);
  expect result == 0, "impl test 18 failed";
  result := ThreeSwimmers(4, 2, 100, 200);
  expect result == 0, "impl test 19 failed";
  result := ThreeSwimmers(1000000000000000000, 10, 7, 59465946);
  expect result == 0, "impl test 20 failed";

  print "All tests passed\n";
}