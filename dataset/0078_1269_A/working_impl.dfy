method Equation(n: int) returns (a: int, b: int)
{
  a := n * 9;
  b := n * 8;
}

method Main()
{
  var a: int, b: int;

  a, b := Equation(1);
  expect a == 9 && b == 8, "Test 1 failed";

  a, b := Equation(512);
  expect a == 4608 && b == 4096, "Test 2 failed";

  a, b := Equation(10000000);
  expect a == 90000000 && b == 80000000, "Test 3 failed";

  a, b := Equation(2);
  expect a == 18 && b == 16, "Test 4 failed";

  a, b := Equation(3);
  expect a == 27 && b == 24, "Test 5 failed";

  a, b := Equation(4);
  expect a == 36 && b == 32, "Test 6 failed";

  a, b := Equation(8958020);
  expect a == 80622180 && b == 71664160, "Test 7 failed";

  a, b := Equation(6);
  expect a == 54 && b == 48, "Test 8 failed";

  a, b := Equation(7);
  expect a == 63 && b == 56, "Test 9 failed";

  a, b := Equation(8);
  expect a == 72 && b == 64, "Test 10 failed";

  a, b := Equation(9);
  expect a == 81 && b == 72, "Test 11 failed";

  a, b := Equation(10);
  expect a == 90 && b == 80, "Test 12 failed";

  a, b := Equation(11);
  expect a == 99 && b == 88, "Test 13 failed";

  a, b := Equation(12);
  expect a == 108 && b == 96, "Test 14 failed";

  a, b := Equation(13);
  expect a == 117 && b == 104, "Test 15 failed";

  a, b := Equation(14);
  expect a == 126 && b == 112, "Test 16 failed";

  a, b := Equation(15);
  expect a == 135 && b == 120, "Test 17 failed";

  a, b := Equation(16);
  expect a == 144 && b == 128, "Test 18 failed";

  a, b := Equation(17);
  expect a == 153 && b == 136, "Test 19 failed";

  a, b := Equation(18);
  expect a == 162 && b == 144, "Test 20 failed";

  print "All tests passed\n";
}