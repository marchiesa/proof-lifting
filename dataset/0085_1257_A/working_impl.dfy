method TwoRivalStudents(n: int, x: int, a: int, b: int) returns (distance: int)
{
  var la := a;
  var lb := b;
  var rx := x;
  if la > lb {
    var tmp := la;
    la := lb;
    lb := tmp;
  }
  var da := if la - 1 < rx then la - 1 else rx;
  la := la - da;
  rx := rx - da;
  var db := if n - lb < rx then n - lb else rx;
  lb := lb + db;
  distance := lb - la;
}

method Main()
{
  var result: int;

  // Test 1
  result := TwoRivalStudents(5, 1, 3, 2);
  expect result == 2, "Test 1.1 failed";
  result := TwoRivalStudents(100, 33, 100, 1);
  expect result == 99, "Test 1.2 failed";
  result := TwoRivalStudents(6, 0, 2, 3);
  expect result == 1, "Test 1.3 failed";

  // Test 2
  result := TwoRivalStudents(100, 100, 100, 1);
  expect result == 99, "Test 2.1 failed";
  result := TwoRivalStudents(100, 100, 1, 100);
  expect result == 99, "Test 2.2 failed";
  result := TwoRivalStudents(100, 0, 100, 1);
  expect result == 99, "Test 2.3 failed";
  result := TwoRivalStudents(100, 0, 1, 100);
  expect result == 99, "Test 2.4 failed";
  result := TwoRivalStudents(2, 0, 1, 2);
  expect result == 1, "Test 2.5 failed";
  result := TwoRivalStudents(2, 100, 1, 2);
  expect result == 1, "Test 2.6 failed";
  result := TwoRivalStudents(2, 0, 2, 1);
  expect result == 1, "Test 2.7 failed";
  result := TwoRivalStudents(2, 100, 2, 1);
  expect result == 1, "Test 2.8 failed";
  result := TwoRivalStudents(100, 0, 1, 2);
  expect result == 1, "Test 2.9 failed";
  result := TwoRivalStudents(100, 98, 1, 2);
  expect result == 99, "Test 2.10 failed";
  result := TwoRivalStudents(100, 97, 1, 2);
  expect result == 98, "Test 2.11 failed";
  result := TwoRivalStudents(100, 0, 2, 1);
  expect result == 1, "Test 2.12 failed";
  result := TwoRivalStudents(100, 98, 2, 1);
  expect result == 99, "Test 2.13 failed";
  result := TwoRivalStudents(100, 97, 2, 1);
  expect result == 98, "Test 2.14 failed";
  result := TwoRivalStudents(100, 0, 99, 100);
  expect result == 1, "Test 2.15 failed";
  result := TwoRivalStudents(100, 98, 99, 100);
  expect result == 99, "Test 2.16 failed";
  result := TwoRivalStudents(100, 97, 99, 100);
  expect result == 98, "Test 2.17 failed";
  result := TwoRivalStudents(100, 0, 100, 99);
  expect result == 1, "Test 2.18 failed";
  result := TwoRivalStudents(100, 98, 100, 99);
  expect result == 99, "Test 2.19 failed";
  result := TwoRivalStudents(100, 97, 100, 99);
  expect result == 98, "Test 2.20 failed";
  result := TwoRivalStudents(100, 0, 13, 37);
  expect result == 24, "Test 2.21 failed";
  result := TwoRivalStudents(100, 0, 66, 11);
  expect result == 55, "Test 2.22 failed";

  // Test 3
  result := TwoRivalStudents(59, 1, 1, 2);
  expect result == 2, "Test 3.1 failed";

  // Test 4
  result := TwoRivalStudents(5, 2, 3, 2);
  expect result == 3, "Test 4.1 failed";

  // Test 5
  result := TwoRivalStudents(53, 1, 3, 2);
  expect result == 2, "Test 5.1 failed";

  print "All tests passed\n";
}