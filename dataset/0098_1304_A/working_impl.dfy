method TwoRabbits(x: int, y: int, a: int, b: int) returns (t: int)
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
  // Test 1 / Test 2
  var t1 := TwoRabbits(0, 10, 2, 3);
  expect t1 == 2, "Test (0,10,2,3): expected 2";

  // Test 1 / Test 3
  var t2 := TwoRabbits(0, 10, 3, 3);
  expect t2 == -1, "Test (0,10,3,3): expected -1";

  // Test 1
  var t3 := TwoRabbits(900000000, 1000000000, 1, 9999999);
  expect t3 == 10, "Test (900000000,1000000000,1,9999999): expected 10";

  // Test 1 / Test 4
  var t4 := TwoRabbits(1, 2, 1, 1);
  expect t4 == -1, "Test (1,2,1,1): expected -1";

  // Test 1 / Test 5
  var t5 := TwoRabbits(1, 3, 1, 1);
  expect t5 == 1, "Test (1,3,1,1): expected 1";

  // Test 6
  var t6 := TwoRabbits(0, 50, 5, 5);
  expect t6 == 5, "Test (0,50,5,5): expected 5";

  // Test 7
  var t7 := TwoRabbits(0, 6, 1, 2);
  expect t7 == 2, "Test (0,6,1,2): expected 2";

  // Test 8
  var t8 := TwoRabbits(10, 20, 3, 7);
  expect t8 == 1, "Test (10,20,3,7): expected 1";

  // Test 9
  var t9a := TwoRabbits(0, 4, 2, 2);
  expect t9a == 1, "Test (0,4,2,2): expected 1";

  var t9b := TwoRabbits(5, 15, 1, 4);
  expect t9b == 2, "Test (5,15,1,4): expected 2";

  var t9c := TwoRabbits(0, 7, 3, 4);
  expect t9c == 1, "Test (0,7,3,4): expected 1";

  // Test 10
  var t10a := TwoRabbits(0, 1, 1, 1);
  expect t10a == -1, "Test (0,1,1,1): expected -1";

  var t10b := TwoRabbits(0, 2, 1, 1);
  expect t10b == 1, "Test (0,2,1,1): expected 1";

  var t10c := TwoRabbits(0, 3, 1, 2);
  expect t10c == 1, "Test (0,3,1,2): expected 1";

  var t10d := TwoRabbits(1, 5, 2, 2);
  expect t10d == 1, "Test (1,5,2,2): expected 1";

  // Test 11
  var t11a := TwoRabbits(0, 50, 7, 3);
  expect t11a == 5, "Test (0,50,7,3): expected 5";

  var t11b := TwoRabbits(3, 9, 1, 2);
  expect t11b == 2, "Test (3,9,1,2): expected 2";

  print "All tests passed\n";
}