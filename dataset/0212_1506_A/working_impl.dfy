method StrangeTable(n: int, m: int, x: int) returns (result: int)
{
  var x0 := x - 1;
  var r := x0 / n;
  var c := x0 % n;
  result := c * m + r + 1;
}

method Main()
{
  var r: int;

  // Test 1
  r := StrangeTable(1, 1, 1);
  expect r == 1, "Test 1.1 failed";
  r := StrangeTable(2, 2, 3);
  expect r == 2, "Test 1.2 failed";
  r := StrangeTable(3, 5, 11);
  expect r == 9, "Test 1.3 failed";
  r := StrangeTable(100, 100, 7312);
  expect r == 1174, "Test 1.4 failed";
  r := StrangeTable(1000000, 1000000, 1000000000000);
  expect r == 1000000000000, "Test 1.5 failed";

  // Test 2
  r := StrangeTable(1, 1, 1);
  expect r == 1, "Test 2.1 failed";
  r := StrangeTable(2, 3, 5);
  expect r == 3, "Test 2.2 failed";
  r := StrangeTable(4, 4, 16);
  expect r == 16, "Test 2.3 failed";

  // Test 3
  r := StrangeTable(3, 5, 11);
  expect r == 9, "Test 3.1 failed";

  // Test 4
  r := StrangeTable(5, 5, 25);
  expect r == 25, "Test 4.1 failed";
  r := StrangeTable(5, 5, 1);
  expect r == 1, "Test 4.2 failed";

  // Test 5
  r := StrangeTable(1, 10, 7);
  expect r == 7, "Test 5.1 failed";
  r := StrangeTable(10, 1, 7);
  expect r == 7, "Test 5.2 failed";
  r := StrangeTable(3, 3, 9);
  expect r == 9, "Test 5.3 failed";
  r := StrangeTable(2, 5, 10);
  expect r == 10, "Test 5.4 failed";

  // Test 6
  r := StrangeTable(7, 7, 49);
  expect r == 49, "Test 6.1 failed";

  // Test 7
  r := StrangeTable(2, 2, 1);
  expect r == 1, "Test 7.1 failed";
  r := StrangeTable(2, 2, 2);
  expect r == 3, "Test 7.2 failed";
  r := StrangeTable(2, 2, 4);
  expect r == 4, "Test 7.3 failed";

  // Test 8
  r := StrangeTable(1, 1, 1);
  expect r == 1, "Test 8.1 failed";
  r := StrangeTable(1, 5, 3);
  expect r == 3, "Test 8.2 failed";
  r := StrangeTable(5, 1, 3);
  expect r == 3, "Test 8.3 failed";
  r := StrangeTable(3, 3, 5);
  expect r == 5, "Test 8.4 failed";
  r := StrangeTable(4, 2, 7);
  expect r == 6, "Test 8.5 failed";

  // Test 9
  r := StrangeTable(6, 8, 48);
  expect r == 48, "Test 9.1 failed";
  r := StrangeTable(8, 6, 48);
  expect r == 48, "Test 9.2 failed";

  // Test 10
  r := StrangeTable(10, 10, 1);
  expect r == 1, "Test 10.1 failed";
  r := StrangeTable(10, 10, 50);
  expect r == 95, "Test 10.2 failed";
  r := StrangeTable(10, 10, 100);
  expect r == 100, "Test 10.3 failed";
  r := StrangeTable(10, 10, 37);
  expect r == 64, "Test 10.4 failed";

  // Test 11
  r := StrangeTable(3, 4, 12);
  expect r == 12, "Test 11.1 failed";
  r := StrangeTable(4, 3, 12);
  expect r == 12, "Test 11.2 failed";
  r := StrangeTable(2, 7, 14);
  expect r == 14, "Test 11.3 failed";

  print "All tests passed\n";
}