function Count(a: seq<int>, v: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[|a|-1] == v then 1 else 0) + Count(a[..|a|-1], v)
}

predicate IsUniqueBid(a: seq<int>, i: int)
  requires 0 <= i < |a|
{
  Count(a, a[i]) == 1
}

predicate NoUniqueBids(a: seq<int>)
{
  forall i | 0 <= i < |a| :: Count(a, a[i]) != 1
}

predicate IsMinimumUniqueBid(a: seq<int>, i: int)
  requires 0 <= i < |a|
{
  IsUniqueBid(a, i) &&
  forall j | 0 <= j < |a| :: (Count(a, a[j]) == 1 ==> a[i] <= a[j])
}

predicate Postcondition(a: seq<int>, winner: int)
{
  (NoUniqueBids(a) <==> (winner == -1)) &&
  (winner != -1 ==> (1 <= winner <= |a| && IsMinimumUniqueBid(a, winner - 1)))
}

method UniqueBidAuction(a: seq<int>) returns (winner: int)
  ensures NoUniqueBids(a) <==> (winner == -1)
  ensures winner != -1 ==> (1 <= winner <= |a| && IsMinimumUniqueBid(a, winner - 1))
{
  winner := -1;
  var minVal := 0;
  var found := false;

  var i := 0;
  while i < |a|
  {
    var count := 0;
    var j := 0;
    while j < |a|
    {
      if a[j] == a[i] {
        count := count + 1;
      }
      j := j + 1;
    }
    if count == 1 && (!found || a[i] < minVal) {
      minVal := a[i];
      winner := i + 1;
      found := true;
    }
    i := i + 1;
  }
  return;
}

method Main()
{
  // ========== SPEC POSITIVE TESTS ==========
  // Postcondition(input, correct_output) must be true

  // From Test 1.1: [1,1] -> -1 (all duplicates, no winner)
  expect Postcondition([1, 1], -1), "spec positive 1";

  // From Test 1.2: [2,1,3] -> 2 (all unique, min=1 at index 1)
  expect Postcondition([2, 1, 3], 2), "spec positive 2";

  // From Test 1.4: [1] -> 1 (single element, unique)
  expect Postcondition([1], 1), "spec positive 3";

  // From Test 4.8: [1,1,2] -> 3 (only 2 is unique, at index 2)
  expect Postcondition([1, 1, 2], 3), "spec positive 4";

  // Additional small: [1,2] -> 1 (both unique, min=1 at index 0)
  expect Postcondition([1, 2], 1), "spec positive 5";

  // From Test 2.1 scaled: [1,1,1] -> -1 (all duplicates)
  expect Postcondition([1, 1, 1], -1), "spec positive 6";

  // ========== SPEC NEGATIVE TESTS ==========
  // Postcondition(input, wrong_output) must be false

  // From Neg 1: [1,1] wrong=0 (correct=-1; violates NoUniqueBids biconditional)
  expect !Postcondition([1, 1], 0), "spec negative 1";

  // From Neg 2 scaled: [1,1,1] wrong=0 (correct=-1; same pattern)
  expect !Postcondition([1, 1, 1], 0), "spec negative 2";

  // From Neg 3 scaled: [2,1,3] wrong=3 (correct=2; index 2 has value 3, not minimum unique)
  expect !Postcondition([2, 1, 3], 3), "spec negative 3";

  // From Neg 4 scaled: [1,1,2] wrong=1 (correct=3; index 0 has value 1 which is not unique)
  expect !Postcondition([1, 1, 2], 1), "spec negative 4";

  // From Neg 5: [1] wrong=0 (correct=1; out of valid range)
  expect !Postcondition([1], 0), "spec negative 5";

  // ========== IMPLEMENTATION TESTS ==========
  var r: int;

  // Test 1
  r := UniqueBidAuction([1, 1]);
  expect r == -1, "impl test 1.1 failed";

  r := UniqueBidAuction([2, 1, 3]);
  expect r == 2, "impl test 1.2 failed";

  r := UniqueBidAuction([2, 2, 2, 3]);
  expect r == 4, "impl test 1.3 failed";

  r := UniqueBidAuction([1]);
  expect r == 1, "impl test 1.4 failed";

  r := UniqueBidAuction([2, 3, 2, 4, 2]);
  expect r == 2, "impl test 1.5 failed";

  r := UniqueBidAuction([1, 1, 5, 5, 4, 4]);
  expect r == -1, "impl test 1.6 failed";

  // Test 2
  r := UniqueBidAuction([1, 1, 1, 3, 3, 3]);
  expect r == -1, "impl test 2.1 failed";

  r := UniqueBidAuction([1, 1, 1, 3]);
  expect r == 4, "impl test 2.2 failed";

  // Test 3
  r := UniqueBidAuction([16, 3, 11, 9, 3, 13, 11, 9, 14, 10, 10, 19, 19, 15, 11, 8, 8, 7, 3]);
  expect r == 18, "impl test 3.1 failed";

  r := UniqueBidAuction([8, 6, 1, 4, 1, 4, 2, 9, 7, 10]);
  expect r == 7, "impl test 3.2 failed";

  r := UniqueBidAuction([7, 1, 1, 4, 4, 1, 2]);
  expect r == 7, "impl test 3.3 failed";

  r := UniqueBidAuction([1]);
  expect r == 1, "impl test 3.4 failed";

  // Test 4
  r := UniqueBidAuction([10, 1, 3, 2, 11, 5, 12, 11, 12, 12, 9, 4]);
  expect r == 2, "impl test 4.1 failed";

  r := UniqueBidAuction([10, 9, 7, 6, 6, 3, 8, 10, 1, 7, 9]);
  expect r == 9, "impl test 4.2 failed";

  r := UniqueBidAuction([3, 11, 8, 9, 5, 9, 6, 5, 11, 12, 8, 7]);
  expect r == 1, "impl test 4.3 failed";

  r := UniqueBidAuction([6, 6, 13, 12, 7, 6, 6, 7, 14, 7, 14, 13, 11, 3, 11]);
  expect r == 14, "impl test 4.4 failed";

  r := UniqueBidAuction([31, 32, 2, 37, 19, 39, 21, 19, 24, 14, 17, 11, 33, 7, 17, 30, 33, 27, 16, 26, 37, 29, 19, 32, 20, 32, 24, 20, 20, 24, 32, 2, 7, 33, 30, 25, 23, 11, 35, 39]);
  expect r == 10, "impl test 4.5 failed";

  r := UniqueBidAuction([11, 9, 16, 2, 10, 5, 10, 4, 13, 11, 8, 1, 13, 7, 4, 12]);
  expect r == 12, "impl test 4.6 failed";

  r := UniqueBidAuction([7, 3, 24, 2, 18, 14, 41, 10, 43, 43, 12, 7, 11, 15, 4, 6, 22, 39, 11, 26, 14, 22, 4, 20, 39, 6, 22, 19, 37, 7, 6, 38, 10, 23, 39, 27, 37, 33, 30, 27, 24, 41, 33, 34, 3, 30]);
  expect r == 4, "impl test 4.7 failed";

  r := UniqueBidAuction([1, 1, 2]);
  expect r == 3, "impl test 4.8 failed";

  // Test 5
  r := UniqueBidAuction([1, 1]);
  expect r == -1, "impl test 5.1 failed";

  r := UniqueBidAuction([1]);
  expect r == 1, "impl test 5.2 failed";

  print "All tests passed\n";
}