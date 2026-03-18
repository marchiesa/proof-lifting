method EhabConstruction(x: int) returns (a: int, b: int, found: bool)
{
  a := 0;
  b := 0;
  found := false;

  var ai := 1;
  while ai <= x && !found
  {
    var bi := 1;
    while bi <= ai && !found
    {
      if ai % bi == 0 && ai * bi > x && ai / bi < x {
        a := ai;
        b := bi;
        found := true;
      }
      bi := bi + 1;
    }
    ai := ai + 1;
  }
}

method Main()
{
  var a: int, b: int, found: bool;

  // Test 1: x=10 → 4 4
  a, b, found := EhabConstruction(10);
  expect found && a == 4 && b == 4, "Test 1 failed";

  // Test 2: x=1 → -1
  a, b, found := EhabConstruction(1);
  expect !found, "Test 2 failed";

  // Test 3: x=5 → 3 3
  a, b, found := EhabConstruction(5);
  expect found && a == 3 && b == 3, "Test 3 failed";

  // Test 4: x=8 → 3 3
  a, b, found := EhabConstruction(8);
  expect found && a == 3 && b == 3, "Test 4 failed";

  // Test 5: x=20 → 5 5
  a, b, found := EhabConstruction(20);
  expect found && a == 5 && b == 5, "Test 5 failed";

  // Test 6: x=55 → 8 8
  a, b, found := EhabConstruction(55);
  expect found && a == 8 && b == 8, "Test 6 failed";

  // Test 7: x=78 → 9 9
  a, b, found := EhabConstruction(78);
  expect found && a == 9 && b == 9, "Test 7 failed";

  // Test 8: x=89 → 10 10
  a, b, found := EhabConstruction(89);
  expect found && a == 10 && b == 10, "Test 8 failed";

  // Test 9: x=100 → 11 11
  a, b, found := EhabConstruction(100);
  expect found && a == 11 && b == 11, "Test 9 failed";

  // Test 10: x=2 → 2 2
  a, b, found := EhabConstruction(2);
  expect found && a == 2 && b == 2, "Test 10 failed";

  // Test 11: x=3 → 2 2
  a, b, found := EhabConstruction(3);
  expect found && a == 2 && b == 2, "Test 11 failed";

  // Test 12: x=4 → 3 3
  a, b, found := EhabConstruction(4);
  expect found && a == 3 && b == 3, "Test 12 failed";

  // Test 13: x=6 → 3 3
  a, b, found := EhabConstruction(6);
  expect found && a == 3 && b == 3, "Test 13 failed";

  // Test 14: x=7 → 3 3
  a, b, found := EhabConstruction(7);
  expect found && a == 3 && b == 3, "Test 14 failed";

  // Test 15: x=9 → 4 4
  a, b, found := EhabConstruction(9);
  expect found && a == 4 && b == 4, "Test 15 failed";

  // Test 16: x=11 → 4 4
  a, b, found := EhabConstruction(11);
  expect found && a == 4 && b == 4, "Test 16 failed";

  // Test 17: x=12 → 4 4
  a, b, found := EhabConstruction(12);
  expect found && a == 4 && b == 4, "Test 17 failed";

  // Test 18: x=13 → 4 4
  a, b, found := EhabConstruction(13);
  expect found && a == 4 && b == 4, "Test 18 failed";

  // Test 19: x=14 → 4 4
  a, b, found := EhabConstruction(14);
  expect found && a == 4 && b == 4, "Test 19 failed";

  // Test 20: x=15 → 4 4
  a, b, found := EhabConstruction(15);
  expect found && a == 4 && b == 4, "Test 20 failed";

  print "All tests passed\n";
}