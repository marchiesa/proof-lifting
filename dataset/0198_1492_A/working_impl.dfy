method ThreeSwimmers(p: int, a: int, b: int, c: int) returns (wait: int)
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

  // Test 1
  result := ThreeSwimmers(9, 5, 4, 8);
  expect result == 1, "Test 1.1 failed";

  result := ThreeSwimmers(2, 6, 10, 9);
  expect result == 4, "Test 1.2 failed";

  result := ThreeSwimmers(10, 2, 5, 10);
  expect result == 0, "Test 1.3 failed";

  result := ThreeSwimmers(10, 9, 9, 9);
  expect result == 8, "Test 1.4 failed";

  // Test 2
  result := ThreeSwimmers(1, 2, 3, 4);
  expect result == 1, "Test 2.1 failed";

  result := ThreeSwimmers(1000000000000000000, 1000000000000000000, 1000000000000000000, 1000000000000000000);
  expect result == 0, "Test 2.2 failed";

  // Test 3
  result := ThreeSwimmers(2, 1, 1, 1);
  expect result == 0, "Test 3 failed";

  // Test 4
  result := ThreeSwimmers(4, 2, 2, 2);
  expect result == 0, "Test 4 failed";

  // Test 5
  result := ThreeSwimmers(12, 6, 6, 6);
  expect result == 0, "Test 5 failed";

  // Test 6
  result := ThreeSwimmers(10, 5, 7, 6);
  expect result == 0, "Test 6 failed";

  // Test 7
  result := ThreeSwimmers(20, 2, 5, 10);
  expect result == 0, "Test 7 failed";

  // Test 8
  result := ThreeSwimmers(6, 2, 2, 2);
  expect result == 0, "Test 8 failed";

  // Test 9
  result := ThreeSwimmers(6, 3, 1000, 2000);
  expect result == 0, "Test 9.1 failed";

  result := ThreeSwimmers(9, 5, 4, 8);
  expect result == 1, "Test 9.2 failed";

  result := ThreeSwimmers(2, 6, 10, 9);
  expect result == 4, "Test 9.3 failed";

  result := ThreeSwimmers(10, 2, 5, 10);
  expect result == 0, "Test 9.4 failed";

  result := ThreeSwimmers(10, 9, 9, 9);
  expect result == 8, "Test 9.5 failed";

  // Test 10
  result := ThreeSwimmers(8, 2, 3, 5);
  expect result == 0, "Test 10 failed";

  // Test 11
  result := ThreeSwimmers(20, 10, 10, 10);
  expect result == 0, "Test 11 failed";

  // Test 12
  result := ThreeSwimmers(8, 4, 4, 4);
  expect result == 0, "Test 12 failed";

  // Test 13
  result := ThreeSwimmers(100, 10, 11, 12);
  expect result == 0, "Test 13 failed";

  // Test 14
  result := ThreeSwimmers(10, 5, 3, 4);
  expect result == 0, "Test 14 failed";

  // Test 15
  result := ThreeSwimmers(10, 2, 1000, 1000);
  expect result == 0, "Test 15 failed";

  // Test 16
  result := ThreeSwimmers(3, 1, 1, 1);
  expect result == 0, "Test 16 failed";

  // Test 17
  result := ThreeSwimmers(10, 2, 3, 4);
  expect result == 0, "Test 17 failed";

  // Test 18
  result := ThreeSwimmers(10, 2, 2, 2);
  expect result == 0, "Test 18 failed";

  // Test 19
  result := ThreeSwimmers(4, 2, 100, 200);
  expect result == 0, "Test 19 failed";

  // Test 20
  result := ThreeSwimmers(1000000000000000000, 10, 7, 59465946);
  expect result == 0, "Test 20 failed";

  print "All tests passed\n";
}