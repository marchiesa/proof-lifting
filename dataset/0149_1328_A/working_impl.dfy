method DivisibilityProblem(a: int, b: int) returns (moves: int)
{
  moves := (b - a % b) % b;
}

method Main()
{
  var result: int;

  // Test 1
  result := DivisibilityProblem(10, 4);
  expect result == 2, "Test (10, 4) failed";

  result := DivisibilityProblem(13, 9);
  expect result == 5, "Test (13, 9) failed";

  result := DivisibilityProblem(100, 13);
  expect result == 4, "Test (100, 13) failed";

  result := DivisibilityProblem(123, 456);
  expect result == 333, "Test (123, 456) failed";

  result := DivisibilityProblem(92, 46);
  expect result == 0, "Test (92, 46) failed";

  // Test 2
  result := DivisibilityProblem(914, 78);
  expect result == 22, "Test (914, 78) failed";

  // Test 3
  result := DivisibilityProblem(2232, 7);
  expect result == 1, "Test (2232, 7) failed";

  // Test 4
  result := DivisibilityProblem(100, 9090);
  expect result == 8990, "Test (100, 9090) failed";

  // Test 5
  result := DivisibilityProblem(515151, 2);
  expect result == 1, "Test (515151, 2) failed";

  // Test 6
  result := DivisibilityProblem(9987, 1);
  expect result == 0, "Test (9987, 1) failed";

  // Test 7
  result := DivisibilityProblem(9986, 1);
  expect result == 0, "Test (9986, 1) failed";

  // Test 8
  result := DivisibilityProblem(1, 3218);
  expect result == 3217, "Test (1, 3218) failed";

  result := DivisibilityProblem(28, 10924);
  expect result == 10896, "Test (28, 10924) failed";

  result := DivisibilityProblem(908802, 141084);
  expect result == 78786, "Test (908802, 141084) failed";

  result := DivisibilityProblem(82149, 9274);
  expect result == 1317, "Test (82149, 9274) failed";

  result := DivisibilityProblem(893257, 10248);
  expect result == 8567, "Test (893257, 10248) failed";

  result := DivisibilityProblem(2750048, 802705);
  expect result == 460772, "Test (2750048, 802705) failed";

  result := DivisibilityProblem(2857, 142);
  expect result == 125, "Test (2857, 142) failed";

  result := DivisibilityProblem(980, 209385);
  expect result == 208405, "Test (980, 209385) failed";

  result := DivisibilityProblem(1, 3218);
  expect result == 3217, "Test (1, 3218) repeat-1 failed";

  result := DivisibilityProblem(28, 10924);
  expect result == 10896, "Test (28, 10924) repeat-1 failed";

  result := DivisibilityProblem(908802, 141084);
  expect result == 78786, "Test (908802, 141084) repeat-1 failed";

  result := DivisibilityProblem(82149, 9274);
  expect result == 1317, "Test (82149, 9274) repeat-1 failed";

  result := DivisibilityProblem(893257, 10248);
  expect result == 8567, "Test (893257, 10248) repeat-1 failed";

  result := DivisibilityProblem(2750048, 802705);
  expect result == 460772, "Test (2750048, 802705) repeat-1 failed";

  result := DivisibilityProblem(2857, 142);
  expect result == 125, "Test (2857, 142) repeat-1 failed";

  result := DivisibilityProblem(980, 209385);
  expect result == 208405, "Test (980, 209385) repeat-1 failed";

  result := DivisibilityProblem(1, 3218);
  expect result == 3217, "Test (1, 3218) repeat-2 failed";

  result := DivisibilityProblem(28, 10924);
  expect result == 10896, "Test (28, 10924) repeat-2 failed";

  result := DivisibilityProblem(908802, 141084);
  expect result == 78786, "Test (908802, 141084) repeat-2 failed";

  result := DivisibilityProblem(82149, 9274);
  expect result == 1317, "Test (82149, 9274) repeat-2 failed";

  result := DivisibilityProblem(893257, 10248);
  expect result == 8567, "Test (893257, 10248) repeat-2 failed";

  print "All tests passed\n";
}