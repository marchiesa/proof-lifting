predicate IsDivisibleAfterMoves(a: int, b: int, moves: int)
  requires b > 0
{
  moves >= 0 && (a + moves) % b == 0
}

predicate IsMinimumMoves(a: int, b: int, moves: int)
  requires b > 0
{
  IsDivisibleAfterMoves(a, b, moves) &&
  forall m | 0 <= m < moves :: !IsDivisibleAfterMoves(a, b, m)
}

method DivisibilityProblem(a: int, b: int) returns (moves: int)
  requires a >= 1 && b >= 1
  ensures IsMinimumMoves(a, b, moves)
{
  moves := (b - a % b) % b;
}

method Main()
{
  var result: int;

  // === SPEC POSITIVE TESTS ===
  // Top-level ensures predicate: IsMinimumMoves(a, b, moves)
  // Using inputs where moves is small to keep bounded quantifier fast
  expect IsMinimumMoves(10, 4, 2), "spec positive 1";       // Test 1, pair 1
  expect IsMinimumMoves(13, 9, 5), "spec positive 2";       // Test 1, pair 2
  expect IsMinimumMoves(100, 13, 4), "spec positive 3";     // Test 1, pair 3
  expect IsMinimumMoves(92, 46, 0), "spec positive 4";      // Test 1, pair 5
  expect IsMinimumMoves(2232, 7, 1), "spec positive 5";     // Test 3
  expect IsMinimumMoves(515151, 2, 1), "spec positive 6";   // Test 5
  expect IsMinimumMoves(9987, 1, 0), "spec positive 7";     // Test 6
  expect IsMinimumMoves(9986, 1, 0), "spec positive 8";     // Test 7

  // === SPEC NEGATIVE TESTS ===
  // Top-level ensures predicate must reject wrong outputs
  expect !IsMinimumMoves(10, 4, 3), "spec negative 1";      // correct 2, wrong 3
  expect !IsMinimumMoves(914, 78, 23), "spec negative 2";   // correct 22, wrong 23
  expect !IsMinimumMoves(2232, 7, 2), "spec negative 3";    // correct 1, wrong 2
  expect !IsMinimumMoves(515151, 2, 2), "spec negative 4";  // correct 1, wrong 2
  expect !IsMinimumMoves(9987, 1, 1), "spec negative 5";    // correct 0, wrong 1
  expect !IsMinimumMoves(9986, 1, 1), "spec negative 6";    // correct 0, wrong 1
  expect !IsMinimumMoves(1, 3218, 3218), "spec negative 7"; // correct 3217, wrong 3218

  // === IMPLEMENTATION TESTS ===
  // Test 1
  result := DivisibilityProblem(10, 4);
  expect result == 2, "impl test (10, 4) failed";
  result := DivisibilityProblem(13, 9);
  expect result == 5, "impl test (13, 9) failed";
  result := DivisibilityProblem(100, 13);
  expect result == 4, "impl test (100, 13) failed";
  result := DivisibilityProblem(123, 456);
  expect result == 333, "impl test (123, 456) failed";
  result := DivisibilityProblem(92, 46);
  expect result == 0, "impl test (92, 46) failed";

  // Test 2
  result := DivisibilityProblem(914, 78);
  expect result == 22, "impl test (914, 78) failed";

  // Test 3
  result := DivisibilityProblem(2232, 7);
  expect result == 1, "impl test (2232, 7) failed";

  // Test 4
  result := DivisibilityProblem(100, 9090);
  expect result == 8990, "impl test (100, 9090) failed";

  // Test 5
  result := DivisibilityProblem(515151, 2);
  expect result == 1, "impl test (515151, 2) failed";

  // Test 6
  result := DivisibilityProblem(9987, 1);
  expect result == 0, "impl test (9987, 1) failed";

  // Test 7
  result := DivisibilityProblem(9986, 1);
  expect result == 0, "impl test (9986, 1) failed";

  // Test 8
  result := DivisibilityProblem(1, 3218);
  expect result == 3217, "impl test (1, 3218) failed";
  result := DivisibilityProblem(28, 10924);
  expect result == 10896, "impl test (28, 10924) failed";
  result := DivisibilityProblem(908802, 141084);
  expect result == 78786, "impl test (908802, 141084) failed";
  result := DivisibilityProblem(82149, 9274);
  expect result == 1317, "impl test (82149, 9274) failed";
  result := DivisibilityProblem(893257, 10248);
  expect result == 8567, "impl test (893257, 10248) failed";
  result := DivisibilityProblem(2750048, 802705);
  expect result == 460772, "impl test (2750048, 802705) failed";
  result := DivisibilityProblem(2857, 142);
  expect result == 125, "impl test (2857, 142) failed";
  result := DivisibilityProblem(980, 209385);
  expect result == 208405, "impl test (980, 209385) failed";

  print "All tests passed\n";
}