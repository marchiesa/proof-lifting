method AnotherOneBitesTheDust(a: int, b: int, c: int) returns (maxLen: int)
{
  var x := a + c;
  var y := b + c;

  if x > y {
    x := y + 1;
  }
  if y > x {
    y := x + 1;
  }

  return x + y;
}

method Main()
{
  var result: int;

  result := AnotherOneBitesTheDust(1, 1, 1);
  expect result == 4, "Test 1 failed";

  result := AnotherOneBitesTheDust(2, 1, 2);
  expect result == 7, "Test 2 failed";

  result := AnotherOneBitesTheDust(3, 5, 2);
  expect result == 11, "Test 3 failed";

  result := AnotherOneBitesTheDust(2, 2, 1);
  expect result == 6, "Test 4 failed";

  result := AnotherOneBitesTheDust(1000000000, 1000000000, 1000000000);
  expect result == 4000000000, "Test 5 failed";

  result := AnotherOneBitesTheDust(3, 1, 3);
  expect result == 9, "Test 6 failed";

  result := AnotherOneBitesTheDust(2, 2, 3);
  expect result == 10, "Test 7 failed";

  result := AnotherOneBitesTheDust(1, 1, 4);
  expect result == 10, "Test 8 failed";

  result := AnotherOneBitesTheDust(1, 1, 2);
  expect result == 6, "Test 9 failed";

  result := AnotherOneBitesTheDust(1, 2, 1);
  expect result == 5, "Test 10 failed";

  result := AnotherOneBitesTheDust(3, 6, 3);
  expect result == 13, "Test 11 failed";

  result := AnotherOneBitesTheDust(5, 5, 4);
  expect result == 18, "Test 12 failed";

  result := AnotherOneBitesTheDust(41764, 97259, 54586);
  expect result == 192701, "Test 13 failed";

  result := AnotherOneBitesTheDust(3698483, 6798912, 18096063);
  expect result == 43589093, "Test 14 failed";

  result := AnotherOneBitesTheDust(13350712, 76770926, 61331309);
  expect result == 149364043, "Test 15 failed";

  result := AnotherOneBitesTheDust(6, 1, 6);
  expect result == 15, "Test 16 failed";

  result := AnotherOneBitesTheDust(3, 7, 5);
  expect result == 17, "Test 17 failed";

  result := AnotherOneBitesTheDust(8, 4, 5);
  expect result == 19, "Test 18 failed";

  result := AnotherOneBitesTheDust(8, 8, 7);
  expect result == 30, "Test 19 failed";

  result := AnotherOneBitesTheDust(3, 9, 1);
  expect result == 9, "Test 20 failed";

  print "All tests passed\n";
}