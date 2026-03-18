method LittleCLoves3(n: int) returns (a: int, b: int, c: int)
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
  var a1, b1, c1 := LittleCLoves3(3);
  expect a1 == 1 && b1 == 1 && c1 == 1, "Test 1 failed";

  var a2, b2, c2 := LittleCLoves3(233);
  expect a2 == 1 && b2 == 2 && c2 == 230, "Test 2 failed";

  var a3, b3, c3 := LittleCLoves3(4);
  expect a3 == 1 && b3 == 1 && c3 == 2, "Test 3 failed";

  var a4, b4, c4 := LittleCLoves3(5);
  expect a4 == 1 && b4 == 2 && c4 == 2, "Test 4 failed";

  var a5, b5, c5 := LittleCLoves3(1234);
  expect a5 == 1 && b5 == 1 && c5 == 1232, "Test 5 failed";

  var a6, b6, c6 := LittleCLoves3(387420489);
  expect a6 == 1 && b6 == 1 && c6 == 387420487, "Test 6 failed";

  var a7, b7, c7 := LittleCLoves3(1000000000);
  expect a7 == 1 && b7 == 1 && c7 == 999999998, "Test 7 failed";

  var a8, b8, c8 := LittleCLoves3(6);
  expect a8 == 1 && b8 == 1 && c8 == 4, "Test 8 failed";

  var a9, b9, c9 := LittleCLoves3(7);
  expect a9 == 1 && b9 == 1 && c9 == 5, "Test 9 failed";

  var a10, b10, c10 := LittleCLoves3(8);
  expect a10 == 1 && b10 == 2 && c10 == 5, "Test 10 failed";

  var a11, b11, c11 := LittleCLoves3(701041167);
  expect a11 == 1 && b11 == 1 && c11 == 701041165, "Test 11 failed";

  var a12, b12, c12 := LittleCLoves3(175744383);
  expect a12 == 1 && b12 == 1 && c12 == 175744381, "Test 12 failed";

  var a13, b13, c13 := LittleCLoves3(60512989);
  expect a13 == 1 && b13 == 1 && c13 == 60512987, "Test 13 failed";

  var a14, b14, c14 := LittleCLoves3(240248899);
  expect a14 == 1 && b14 == 1 && c14 == 240248897, "Test 14 failed";

  var a15, b15, c15 := LittleCLoves3(125017505);
  expect a15 == 1 && b15 == 2 && c15 == 125017502, "Test 15 failed";

  var a16, b16, c16 := LittleCLoves3(599720719);
  expect a16 == 1 && b16 == 1 && c16 == 599720717, "Test 16 failed";

  var a17, b17, c17 := LittleCLoves3(484489325);
  expect a17 == 1 && b17 == 2 && c17 == 484489322, "Test 17 failed";

  var a18, b18, c18 := LittleCLoves3(369257931);
  expect a18 == 1 && b18 == 1 && c18 == 369257929, "Test 18 failed";

  var a19, b19, c19 := LittleCLoves3(548993841);
  expect a19 == 1 && b19 == 1 && c19 == 548993839, "Test 19 failed";

  var a20, b20, c20 := LittleCLoves3(795065278);
  expect a20 == 1 && b20 == 1 && c20 == 795065276, "Test 20 failed";

  print "All tests passed\n";
}