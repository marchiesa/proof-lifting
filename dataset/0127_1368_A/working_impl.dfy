method CPlusEqual(a: int, b: int, n: int) returns (ops: int)
{
  var x := a;
  var y := b;
  if x > y {
    x, y := y, x;
  }
  var i := 1;
  while i < 1000 {
    if i % 2 == 1 {
      x := x + y;
    } else {
      y := y + x;
    }
    if x > n || y > n {
      ops := i;
      return;
    }
    i := i + 1;
  }
  ops := 0;
  return;
}

method Main()
{
  var result: int;

  // Test 1
  result := CPlusEqual(1, 2, 3);
  expect result == 2, "CPlusEqual(1, 2, 3) failed";
  result := CPlusEqual(5, 4, 100);
  expect result == 7, "CPlusEqual(5, 4, 100) failed";

  // Test 2
  result := CPlusEqual(1, 1, 1);
  expect result == 1, "CPlusEqual(1, 1, 1) failed";
  result := CPlusEqual(3, 4, 7);
  expect result == 2, "CPlusEqual(3, 4, 7) failed";
  result := CPlusEqual(4, 5, 13);
  expect result == 2, "CPlusEqual(4, 5, 13) failed";
  result := CPlusEqual(456, 123, 7890123);
  expect result == 21, "CPlusEqual(456, 123, 7890123) failed";
  result := CPlusEqual(1, 1, 1000000000);
  expect result == 43, "CPlusEqual(1, 1, 1000000000) failed";
  result := CPlusEqual(45, 12, 782595420);
  expect result == 36, "CPlusEqual(45, 12, 782595420) failed";
  result := CPlusEqual(1, 1000000000, 1000000000);
  expect result == 1, "CPlusEqual(1, 1000000000, 1000000000) failed";
  result := CPlusEqual(1, 999999999, 1000000000);
  expect result == 2, "CPlusEqual(1, 999999999, 1000000000) failed";
  result := CPlusEqual(1, 99999, 676497416);
  expect result == 20, "CPlusEqual(1, 99999, 676497416) failed";
  result := CPlusEqual(5, 6, 930234861);
  expect result == 40, "CPlusEqual(5, 6, 930234861) failed";
  result := CPlusEqual(8, 9, 881919225);
  expect result == 38, "CPlusEqual(8, 9, 881919225) failed";
  result := CPlusEqual(500000000, 500000000, 1000000000);
  expect result == 2, "CPlusEqual(500000000, 500000000, 1000000000) failed";
  result := CPlusEqual(1000000000, 1000000000, 1000000000);
  expect result == 1, "CPlusEqual(1000000000, 1000000000, 1000000000) failed";
  result := CPlusEqual(999999999, 1000000000, 1000000000);
  expect result == 1, "CPlusEqual(999999999, 1000000000, 1000000000) failed";
  result := CPlusEqual(666, 999999, 987405273);
  expect result == 16, "CPlusEqual(666, 999999, 987405273) failed";
  result := CPlusEqual(5378, 5378, 652851553);
  expect result == 24, "CPlusEqual(5378, 5378, 652851553) failed";

  // Test 3
  // CPlusEqual(1, 1, 1) → 1 already covered above

  // Test 4
  result := CPlusEqual(1, 1, 50);
  expect result == 8, "CPlusEqual(1, 1, 50) failed";

  // Test 5
  // CPlusEqual(1, 2, 3) and CPlusEqual(5, 4, 100) already covered
  // CPlusEqual(1, 1, 1) already covered

  // Test 6
  result := CPlusEqual(25, 25, 50);
  expect result == 2, "CPlusEqual(25, 25, 50) failed";

  // Test 7
  result := CPlusEqual(1, 50, 50);
  expect result == 1, "CPlusEqual(1, 50, 50) failed";

  // Test 8
  result := CPlusEqual(50, 1, 50);
  expect result == 1, "CPlusEqual(50, 1, 50) failed";

  // Test 9
  result := CPlusEqual(3, 7, 20);
  expect result == 3, "CPlusEqual(3, 7, 20) failed";

  // Test 10
  result := CPlusEqual(1, 1, 10);
  expect result == 5, "CPlusEqual(1, 1, 10) failed";
  result := CPlusEqual(2, 3, 15);
  expect result == 4, "CPlusEqual(2, 3, 15) failed";
  result := CPlusEqual(5, 5, 30);
  expect result == 4, "CPlusEqual(5, 5, 30) failed";
  result := CPlusEqual(1, 10, 50);
  expect result == 4, "CPlusEqual(1, 10, 50) failed";
  result := CPlusEqual(7, 3, 25);
  expect result == 3, "CPlusEqual(7, 3, 25) failed";

  // Test 11
  result := CPlusEqual(1, 1, 2);
  expect result == 2, "CPlusEqual(1, 1, 2) failed";

  // Test 12
  result := CPlusEqual(49, 49, 50);
  expect result == 1, "CPlusEqual(49, 49, 50) failed";

  print "All tests passed\n";
}