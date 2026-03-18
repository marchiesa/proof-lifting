predicate AllConsiderEasy(opinions: seq<int>)
{
  forall i | 0 <= i < |opinions| :: opinions[i] == 0
}

predicate SpecValid(opinions: seq<int>, result: string)
{
  (AllConsiderEasy(opinions) ==> result == "EASY") &&
  (!AllConsiderEasy(opinions) ==> result == "HARD")
}

method IsEasyProblem(n: int, opinions: seq<int>) returns (result: string)
  ensures AllConsiderEasy(opinions) ==> result == "EASY"
  ensures !AllConsiderEasy(opinions) ==> result == "HARD"
{
  var allZero := true;
  var i := 0;
  while i < |opinions|
  {
    if opinions[i] != 0 {
      allZero := false;
    }
    i := i + 1;
  }
  if allZero {
    result := "EASY";
  } else {
    result := "HARD";
  }
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // SpecValid encodes both ensures clauses; correct outputs must satisfy it.
  // Scaled to small inputs (length 1-3) for bounded quantifier evaluation.

  // From test 1: [0,0,1] -> "HARD"
  expect SpecValid([0, 0, 1], "HARD"), "spec positive 1";
  // From test 2: [0] -> "EASY"
  expect SpecValid([0], "EASY"), "spec positive 2";
  // From test 3: [1] -> "HARD"
  expect SpecValid([1], "HARD"), "spec positive 3";
  // From test 4 scaled: [0,0,0] -> "EASY"
  expect SpecValid([0, 0, 0], "EASY"), "spec positive 4";
  // From test 6 scaled: [1,0,0] -> "HARD"
  expect SpecValid([1, 0, 0], "HARD"), "spec positive 5";
  // From test 7 scaled: [1,1,1] -> "HARD"
  expect SpecValid([1, 1, 1], "HARD"), "spec positive 6";
  // From test 8 scaled: [0,1,0] -> "HARD"
  expect SpecValid([0, 1, 0], "HARD"), "spec positive 7";
  // From test 17: [0,0] -> "EASY"
  expect SpecValid([0, 0], "EASY"), "spec positive 8";
  // From test 9 scaled: [0,1,1] -> "HARD"
  expect SpecValid([0, 1, 1], "HARD"), "spec positive 9";
  // From test 10 scaled: [1,1,0] -> "HARD"
  expect SpecValid([1, 1, 0], "HARD"), "spec positive 10";

  // === SPEC NEGATIVE TESTS ===
  // Wrong outputs must NOT satisfy the spec.

  // From neg 1 scaled: [0,0,1], wrong="HARD WRONG"
  expect !SpecValid([0, 0, 1], "HARD WRONG"), "spec negative 1";
  // From neg 2: [0], wrong="EASY WRONG"
  expect !SpecValid([0], "EASY WRONG"), "spec negative 2";
  // From neg 3: [1], wrong="HARD WRONG"
  expect !SpecValid([1], "HARD WRONG"), "spec negative 3";
  // From neg 4 scaled: [0,0,0], wrong="EASY WRONG"
  expect !SpecValid([0, 0, 0], "EASY WRONG"), "spec negative 4";
  // From neg 6 scaled: [1,0,0], wrong="HARD WRONG"
  expect !SpecValid([1, 0, 0], "HARD WRONG"), "spec negative 5";
  // From neg 7 scaled: [1,1,1], wrong="HARD WRONG"
  expect !SpecValid([1, 1, 1], "HARD WRONG"), "spec negative 6";
  // From neg 8 scaled: [0,1,0], wrong="HARD WRONG"
  expect !SpecValid([0, 1, 0], "HARD WRONG"), "spec negative 7";
  // From neg 9 scaled: [0,1,1], wrong="HARD WRONG"
  expect !SpecValid([0, 1, 1], "HARD WRONG"), "spec negative 8";
  // From neg 10 scaled: [1,1,0], wrong="HARD WRONG"
  expect !SpecValid([1, 1, 0], "HARD WRONG"), "spec negative 9";
  // From neg 5 scaled: [0,0,1], wrong="HARD WRONG"
  expect !SpecValid([0, 0, 1], "HARD WRONG"), "spec negative 10";

  // === IMPLEMENTATION TESTS ===
  var r: string;

  // Test 1
  r := IsEasyProblem(3, [0, 0, 1]);
  expect r == "HARD", "impl test 1 failed";

  // Test 2
  r := IsEasyProblem(1, [0]);
  expect r == "EASY", "impl test 2 failed";

  // Test 3
  r := IsEasyProblem(1, [1]);
  expect r == "HARD", "impl test 3 failed";

  // Test 4
  r := IsEasyProblem(100, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
  expect r == "EASY", "impl test 4 failed";

  // Test 5
  r := IsEasyProblem(100, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]);
  expect r == "HARD", "impl test 5 failed";

  // Test 6
  r := IsEasyProblem(100, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
  expect r == "HARD", "impl test 6 failed";

  // Test 7
  r := IsEasyProblem(100, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]);
  expect r == "HARD", "impl test 7 failed";

  // Test 8
  r := IsEasyProblem(100, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
  expect r == "HARD", "impl test 8 failed";

  // Test 9
  r := IsEasyProblem(100, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]);
  expect r == "HARD", "impl test 9 failed";

  // Test 10
  r := IsEasyProblem(100, [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
  expect r == "HARD", "impl test 10 failed";

  // Test 11
  r := IsEasyProblem(100, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1]);
  expect r == "HARD", "impl test 11 failed";

  // Test 12
  r := IsEasyProblem(100, [1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
  expect r == "HARD", "impl test 12 failed";

  // Test 13
  r := IsEasyProblem(100, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1]);
  expect r == "HARD", "impl test 13 failed";

  // Test 14
  r := IsEasyProblem(100, [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
  expect r == "HARD", "impl test 14 failed";

  // Test 15
  r := IsEasyProblem(100, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1]);
  expect r == "HARD", "impl test 15 failed";

  // Test 16
  r := IsEasyProblem(100, [1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
  expect r == "HARD", "impl test 16 failed";

  // Test 17
  r := IsEasyProblem(2, [0, 0]);
  expect r == "EASY", "impl test 17 failed";

  // Test 18
  r := IsEasyProblem(3, [0, 0, 0]);
  expect r == "EASY", "impl test 18 failed";

  // Test 19
  r := IsEasyProblem(10, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
  expect r == "EASY", "impl test 19 failed";

  // Test 20
  r := IsEasyProblem(50, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
  expect r == "EASY", "impl test 20 failed";

  print "All tests passed\n";
}