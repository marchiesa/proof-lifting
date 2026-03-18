predicate ApartmentOnFloor(n: int, x: int, f: int)
{
  if f == 1 then
    1 <= n <= 2
  else
    f >= 2 && (f - 2) * x + 3 <= n <= (f - 1) * x + 2
}

method FloorNumber(n: int, x: int) returns (floor: int)
  requires n >= 1
  requires x >= 1
  ensures ApartmentOnFloor(n, x, floor)
{
  if n <= 2 {
    floor := 1;
  } else {
    var m := n - 3;
    floor := m / x + 2;
  }
}

method Main()
{
  var result: int;

  // ===== SPEC POSITIVE TESTS =====
  // Test 1: (7,3)->3, (1,5)->1, (22,5)->5, (987,13)->77
  expect ApartmentOnFloor(7, 3, 3), "spec positive 1a";
  expect ApartmentOnFloor(1, 5, 1), "spec positive 1b";
  expect ApartmentOnFloor(22, 5, 5), "spec positive 1c";
  expect ApartmentOnFloor(987, 13, 77), "spec positive 1d";

  // Test 3: (1,1)->1, (2,1)->1, (3,1)->2
  expect ApartmentOnFloor(1, 1, 1), "spec positive 3a";
  expect ApartmentOnFloor(2, 1, 1), "spec positive 3b";
  expect ApartmentOnFloor(3, 1, 2), "spec positive 3c";

  // Test 4: (5,3)->2
  expect ApartmentOnFloor(5, 3, 2), "spec positive 4";

  // Test 5: (10,4)->3, (15,5)->4
  expect ApartmentOnFloor(10, 4, 3), "spec positive 5a";
  expect ApartmentOnFloor(15, 5, 4), "spec positive 5b";

  // Test 6: (1,10)->1
  expect ApartmentOnFloor(1, 10, 1), "spec positive 6";

  // Test 7: (2,7)->1
  expect ApartmentOnFloor(2, 7, 1), "spec positive 7";

  // Test 8: (3,2)->2
  expect ApartmentOnFloor(3, 2, 2), "spec positive 8";

  // Test 9: (50,10)->6, (4,2)->2
  expect ApartmentOnFloor(50, 10, 6), "spec positive 9a";
  expect ApartmentOnFloor(4, 2, 2), "spec positive 9b";

  // Test 10: (11,3)->4
  expect ApartmentOnFloor(11, 3, 4), "spec positive 10";

  // ===== SPEC NEGATIVE TESTS =====
  // Neg 1: (7,3) wrong=4
  expect !ApartmentOnFloor(7, 3, 4), "spec negative 1";

  // Neg 2: (7,3) wrong=4
  expect !ApartmentOnFloor(7, 3, 4), "spec negative 2";

  // Neg 3: (1,1) wrong=2
  expect !ApartmentOnFloor(1, 1, 2), "spec negative 3";

  // Neg 4: (5,3) wrong=3
  expect !ApartmentOnFloor(5, 3, 3), "spec negative 4";

  // Neg 5: (10,4) wrong=4
  expect !ApartmentOnFloor(10, 4, 4), "spec negative 5";

  // Neg 6: (1,10) wrong=2
  expect !ApartmentOnFloor(1, 10, 2), "spec negative 6";

  // Neg 7: (2,7) wrong=2
  expect !ApartmentOnFloor(2, 7, 2), "spec negative 7";

  // Neg 8: (3,2) wrong=3
  expect !ApartmentOnFloor(3, 2, 3), "spec negative 8";

  // Neg 9: (7,3) wrong=4
  expect !ApartmentOnFloor(7, 3, 4), "spec negative 9";

  // Neg 10: (11,3) wrong=5
  expect !ApartmentOnFloor(11, 3, 5), "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====
  // Test 1
  result := FloorNumber(7, 3);
  expect result == 3, "impl test 1a failed";
  result := FloorNumber(1, 5);
  expect result == 1, "impl test 1b failed";
  result := FloorNumber(22, 5);
  expect result == 5, "impl test 1c failed";
  result := FloorNumber(987, 13);
  expect result == 77, "impl test 1d failed";

  // Test 3
  result := FloorNumber(1, 1);
  expect result == 1, "impl test 3a failed";
  result := FloorNumber(2, 1);
  expect result == 1, "impl test 3b failed";
  result := FloorNumber(3, 1);
  expect result == 2, "impl test 3c failed";

  // Test 4
  result := FloorNumber(5, 3);
  expect result == 2, "impl test 4 failed";

  // Test 5
  result := FloorNumber(10, 4);
  expect result == 3, "impl test 5a failed";
  result := FloorNumber(15, 5);
  expect result == 4, "impl test 5b failed";

  // Test 6
  result := FloorNumber(1, 10);
  expect result == 1, "impl test 6 failed";

  // Test 7
  result := FloorNumber(2, 7);
  expect result == 1, "impl test 7 failed";

  // Test 8
  result := FloorNumber(3, 2);
  expect result == 2, "impl test 8 failed";

  // Test 9
  result := FloorNumber(7, 3);
  expect result == 3, "impl test 9a failed";
  result := FloorNumber(1, 5);
  expect result == 1, "impl test 9b failed";
  result := FloorNumber(22, 5);
  expect result == 5, "impl test 9c failed";
  result := FloorNumber(50, 10);
  expect result == 6, "impl test 9d failed";
  result := FloorNumber(4, 2);
  expect result == 2, "impl test 9e failed";

  // Test 10
  result := FloorNumber(11, 3);
  expect result == 4, "impl test 10 failed";

  // Additional impl tests from original Main
  result := FloorNumber(6, 2);
  expect result == 3, "impl test 11a failed";
  result := FloorNumber(8, 2);
  expect result == 4, "impl test 11b failed";
  result := FloorNumber(10, 2);
  expect result == 5, "impl test 11c failed";
  result := FloorNumber(49, 7);
  expect result == 8, "impl test 12a failed";
  result := FloorNumber(25, 6);
  expect result == 5, "impl test 12b failed";
  result := FloorNumber(2, 9);
  expect result == 1, "impl test 12c failed";
  result := FloorNumber(30, 4);
  expect result == 8, "impl test 12d failed";

  print "All tests passed\n";
}