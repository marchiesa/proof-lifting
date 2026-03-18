method TokitsukazeAndEnhancement(x: int) returns (a: int, b: char)
{
  var r := x % 4;
  if r == 0 {
    a := 1;
    b := 'A';
  } else if r == 1 {
    a := 0;
    b := 'A';
  } else if r == 2 {
    a := 1;
    b := 'B';
  } else {
    a := 2;
    b := 'A';
  }
}

method Main()
{
  var a: int;
  var b: char;

  a, b := TokitsukazeAndEnhancement(33);
  expect a == 0 && b == 'A', "Test 1 failed";

  a, b := TokitsukazeAndEnhancement(98);
  expect a == 1 && b == 'B', "Test 2 failed";

  a, b := TokitsukazeAndEnhancement(100);
  expect a == 1 && b == 'A', "Test 3 failed";

  a, b := TokitsukazeAndEnhancement(30);
  expect a == 1 && b == 'B', "Test 4 failed";

  a, b := TokitsukazeAndEnhancement(43);
  expect a == 2 && b == 'A', "Test 5 failed";

  a, b := TokitsukazeAndEnhancement(85);
  expect a == 0 && b == 'A', "Test 6 failed";

  a, b := TokitsukazeAndEnhancement(91);
  expect a == 2 && b == 'A', "Test 7 failed";

  a, b := TokitsukazeAndEnhancement(50);
  expect a == 1 && b == 'B', "Test 8 failed";

  a, b := TokitsukazeAndEnhancement(67);
  expect a == 2 && b == 'A', "Test 9 failed";

  a, b := TokitsukazeAndEnhancement(95);
  expect a == 2 && b == 'A', "Test 10 failed";

  a, b := TokitsukazeAndEnhancement(32);
  expect a == 1 && b == 'A', "Test 11 failed";

  a, b := TokitsukazeAndEnhancement(60);
  expect a == 1 && b == 'A', "Test 12 failed";

  a, b := TokitsukazeAndEnhancement(88);
  expect a == 1 && b == 'A', "Test 13 failed";

  a, b := TokitsukazeAndEnhancement(36);
  expect a == 1 && b == 'A', "Test 14 failed";

  a, b := TokitsukazeAndEnhancement(83);
  expect a == 2 && b == 'A', "Test 15 failed";

  a, b := TokitsukazeAndEnhancement(42);
  expect a == 1 && b == 'B', "Test 16 failed";

  a, b := TokitsukazeAndEnhancement(59);
  expect a == 2 && b == 'A', "Test 17 failed";

  a, b := TokitsukazeAndEnhancement(76);
  expect a == 1 && b == 'A', "Test 18 failed";

  a, b := TokitsukazeAndEnhancement(93);
  expect a == 0 && b == 'A', "Test 19 failed";

  a, b := TokitsukazeAndEnhancement(52);
  expect a == 1 && b == 'A', "Test 20 failed";

  print "All tests passed\n";
}