predicate IsValidSplit(n: int, a: int, b: int, c: int)
{
  a > 0 && b > 0 && c > 0 &&
  a + b + c == n &&
  a % 3 != 0 && b % 3 != 0 && c % 3 != 0
}

method LittleCLoves3(n: int) returns (a: int, b: int, c: int)
  requires n >= 3
  ensures IsValidSplit(n, a, b, c)
{
  a := 1;
  b := 1;
  c := n - 2;
  if c % 3 == 0 {
    c := c - 1;
    b := b + 1;
  }
}

method Main()
{
  // === SPEC POSITIVE tests ===
  expect IsValidSplit(3, 1, 1, 1), "spec positive 1";
  expect IsValidSplit(4, 1, 1, 2), "spec positive 3";
  expect IsValidSplit(5, 1, 2, 2), "spec positive 4";
  expect IsValidSplit(6, 1, 1, 4), "spec positive 8";
  expect IsValidSplit(7, 1, 1, 5), "spec positive 9";
  expect IsValidSplit(8, 1, 2, 5), "spec positive 10";
  expect IsValidSplit(233, 1, 2, 230), "spec positive 2";
  expect IsValidSplit(1234, 1, 1, 1232), "spec positive 5";
  expect IsValidSplit(387420489, 1, 1, 387420487), "spec positive 6";
  expect IsValidSplit(1000000000, 1, 1, 999999998), "spec positive 7";

  // === SPEC NEGATIVE tests ===
  expect !IsValidSplit(3, 2, 1, 1), "spec negative 1";    // sum=4 != 3
  expect !IsValidSplit(4, 2, 1, 2), "spec negative 3";    // sum=5 != 4
  expect !IsValidSplit(5, 2, 2, 2), "spec negative 4";    // sum=6 != 5
  expect !IsValidSplit(6, 2, 1, 4), "spec negative 8";    // sum=7 != 6
  expect !IsValidSplit(7, 2, 1, 5), "spec negative 9";    // sum=8 != 7
  expect !IsValidSplit(8, 2, 2, 5), "spec negative 10";   // sum=9 != 8
  expect !IsValidSplit(233, 2, 2, 230), "spec negative 2"; // sum=234 != 233
  expect !IsValidSplit(1234, 2, 1, 1232), "spec negative 5"; // sum=1235 != 1234
  expect !IsValidSplit(387420489, 2, 1, 387420487), "spec negative 6"; // sum=387420490 != 387420489
  expect !IsValidSplit(1000000000, 2, 1, 999999998), "spec negative 7"; // sum=1000000001 != 1000000000

  // === IMPLEMENTATION tests ===
  var a1, b1, c1 := LittleCLoves3(3);
  expect a1 == 1 && b1 == 1 && c1 == 1, "impl test 1 failed";

  var a2, b2, c2 := LittleCLoves3(233);
  expect a2 == 1 && b2 == 2 && c2 == 230, "impl test 2 failed";

  var a3, b3, c3 := LittleCLoves3(4);
  expect a3 == 1 && b3 == 1 && c3 == 2, "impl test 3 failed";

  var a4, b4, c4 := LittleCLoves3(5);
  expect a4 == 1 && b4 == 2 && c4 == 2, "impl test 4 failed";

  var a5, b5, c5 := LittleCLoves3(1234);
  expect a5 == 1 && b5 == 1 && c5 == 1232, "impl test 5 failed";

  var a6, b6, c6 := LittleCLoves3(387420489);
  expect a6 == 1 && b6 == 1 && c6 == 387420487, "impl test 6 failed";

  var a7, b7, c7 := LittleCLoves3(1000000000);
  expect a7 == 1 && b7 == 1 && c7 == 999999998, "impl test 7 failed";

  var a8, b8, c8 := LittleCLoves3(6);
  expect a8 == 1 && b8 == 1 && c8 == 4, "impl test 8 failed";

  var a9, b9, c9 := LittleCLoves3(7);
  expect a9 == 1 && b9 == 1 && c9 == 5, "impl test 9 failed";

  var a10, b10, c10 := LittleCLoves3(8);
  expect a10 == 1 && b10 == 2 && c10 == 5, "impl test 10 failed";

  print "All tests passed\n";
}