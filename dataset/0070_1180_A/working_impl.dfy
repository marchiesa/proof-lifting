method Rhombus(n: int) returns (cells: int)
{
  cells := 1;
  var i := 1;
  while i < n
  {
    cells := cells + i * 4;
    i := i + 1;
  }
}

method Main()
{
  var result: int;

  result := Rhombus(1);
  expect result == 1, "Test 1 failed";

  result := Rhombus(2);
  expect result == 5, "Test 2 failed";

  result := Rhombus(3);
  expect result == 13, "Test 3 failed";

  result := Rhombus(11);
  expect result == 221, "Test 4 failed";

  result := Rhombus(21);
  expect result == 841, "Test 5 failed";

  result := Rhombus(31);
  expect result == 1861, "Test 6 failed";

  result := Rhombus(41);
  expect result == 3281, "Test 7 failed";

  result := Rhombus(51);
  expect result == 5101, "Test 8 failed";

  result := Rhombus(100);
  expect result == 19801, "Test 9 failed";

  result := Rhombus(34);
  expect result == 2245, "Test 10 failed";

  result := Rhombus(25);
  expect result == 1201, "Test 11 failed";

  result := Rhombus(37);
  expect result == 2665, "Test 12 failed";

  result := Rhombus(39);
  expect result == 2965, "Test 13 failed";

  result := Rhombus(78);
  expect result == 12013, "Test 14 failed";

  result := Rhombus(87);
  expect result == 14965, "Test 15 failed";

  result := Rhombus(26);
  expect result == 1301, "Test 16 failed";

  result := Rhombus(8);
  expect result == 113, "Test 17 failed";

  result := Rhombus(94);
  expect result == 17485, "Test 18 failed";

  result := Rhombus(68);
  expect result == 9113, "Test 19 failed";

  result := Rhombus(90);
  expect result == 16021, "Test 20 failed";

  print "All tests passed\n";
}