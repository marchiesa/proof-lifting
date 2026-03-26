function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

predicate CanAchieveOddSumIn(source: seq<int>, steps: nat)
  decreases steps
{
  if Sum(source) % 2 != 0 then true
  else if steps == 0 then false
  else exists i | 0 <= i < |source| :: exists j | 0 <= j < |source| ::
    i != j && source[i] != source[j] &&
    CanAchieveOddSumIn(source[i := source[j]], steps - 1)
}

method ArrayWithOddSum(a: seq<int>) returns (result: bool)
  ensures result == CanAchieveOddSumIn(a, |a|)
{
  var sm := 0;
  for i := 0 to |a| {
    sm := sm + a[i];
  }
  if sm % 2 != 0 {
    result := true;
  } else {
    var od := 0;
    var ev := 0;
    for i := 0 to |a| {
      if a[i] % 2 != 0 {
        od := od + 1;
      } else {
        ev := ev + 1;
      }
    }
    if od == 0 || ev == 0 {
      result := false;
    } else {
      result := true;
    }
  }
}

method Main()
{
  var r: bool;

  // ===== SPEC POSITIVE TESTS =====
  // Small inputs only (length 1-3, values 0-5) to keep existential enumeration fast

  // From Test 1.1: [2,3] → true (sum=5, odd)
  expect CanAchieveOddSumIn([2, 3], 2) == true, "spec positive 1";
  // From Test 1.2 scaled: [2,2] → false (all even, same values)
  expect CanAchieveOddSumIn([2, 2], 2) == false, "spec positive 2";
  // From Test 2 scaled: [2] → false (single even)
  expect CanAchieveOddSumIn([2], 1) == false, "spec positive 3";
  // From Test 3.1 scaled: [3] → true (single odd)
  expect CanAchieveOddSumIn([3], 1) == true, "spec positive 4";
  // From Test 3.2: [1,2] → true (sum=3, odd)
  expect CanAchieveOddSumIn([1, 2], 2) == true, "spec positive 5";
  // From Test 5: [1] → true (single odd)
  expect CanAchieveOddSumIn([1], 1) == true, "spec positive 6";
  // From Test 6.1: [1,1,1] → true (sum=3, odd)
  expect CanAchieveOddSumIn([1, 1, 1], 3) == true, "spec positive 7";
  // From Test 6.2: [2,2,2] → false (all even, same)
  expect CanAchieveOddSumIn([2, 2, 2], 3) == false, "spec positive 8";
  // From Test 9: [1,1,2] → true (copy to get odd sum)
  expect CanAchieveOddSumIn([1, 1, 2], 3) == true, "spec positive 9";
  // From Test 10.3 scaled: [1,1] → false (same odd values, even sum)
  expect CanAchieveOddSumIn([1, 1], 2) == false, "spec positive 10";
  // From Test 10.4 scaled: [4,4] → false (same even values)
  expect CanAchieveOddSumIn([4, 4], 2) == false, "spec positive 11";

  // ===== SPEC NEGATIVE TESTS =====
  // Each tests that the spec rejects the wrong output

  // Neg 2 scaled: [2] correct=false, wrong=true
  expect CanAchieveOddSumIn([2], 1) != true, "spec negative 1";
  // Neg 4 scaled: [2,4] correct=false, wrong=true
  expect CanAchieveOddSumIn([2, 4], 2) != true, "spec negative 2";
  // Neg 5: [1] correct=true, wrong=false
  expect CanAchieveOddSumIn([1], 1) != false, "spec negative 3";
  // Neg 7 scaled: [1,2] correct=true, wrong=false
  expect CanAchieveOddSumIn([1, 2], 2) != false, "spec negative 4";
  // Neg 8 scaled: [2,2] correct=false, wrong=true
  expect CanAchieveOddSumIn([2, 2], 2) != true, "spec negative 5";
  // Neg 9: [1,1,2] correct=true, wrong=false
  expect CanAchieveOddSumIn([1, 1, 2], 3) != false, "spec negative 6";

  // ===== IMPLEMENTATION TESTS =====
  // Full-size test pairs (method is O(n), no expensive quantifiers)

  // Test 1
  r := ArrayWithOddSum([2, 3]);
  expect r == true, "impl test 1.1 failed";
  r := ArrayWithOddSum([2, 2, 8, 8]);
  expect r == false, "impl test 1.2 failed";
  r := ArrayWithOddSum([3, 3, 3]);
  expect r == true, "impl test 1.3 failed";
  r := ArrayWithOddSum([5, 5, 5, 5]);
  expect r == false, "impl test 1.4 failed";
  r := ArrayWithOddSum([1, 1, 1, 1]);
  expect r == false, "impl test 1.5 failed";

  // Test 2
  r := ArrayWithOddSum([114]);
  expect r == false, "impl test 2.1 failed";

  // Test 3
  r := ArrayWithOddSum([7]);
  expect r == true, "impl test 3.1 failed";
  r := ArrayWithOddSum([1, 2]);
  expect r == true, "impl test 3.2 failed";
  r := ArrayWithOddSum([3, 3, 3]);
  expect r == true, "impl test 3.3 failed";

  // Test 4
  r := ArrayWithOddSum([2, 4, 6, 8, 10]);
  expect r == false, "impl test 4.1 failed";

  // Test 5
  r := ArrayWithOddSum([1]);
  expect r == true, "impl test 5.1 failed";

  // Test 6
  r := ArrayWithOddSum([1, 1, 1]);
  expect r == true, "impl test 6.1 failed";
  r := ArrayWithOddSum([2, 2, 2]);
  expect r == false, "impl test 6.2 failed";

  // Test 7
  r := ArrayWithOddSum([1, 2, 3, 4]);
  expect r == true, "impl test 7.1 failed";

  // Test 8
  r := ArrayWithOddSum([2, 2, 2, 2, 2, 2]);
  expect r == false, "impl test 8.1 failed";

  // Test 9
  r := ArrayWithOddSum([1, 1, 2]);
  expect r == true, "impl test 9.1 failed";

  // Test 10
  r := ArrayWithOddSum([2]);
  expect r == false, "impl test 10.1 failed";
  r := ArrayWithOddSum([3]);
  expect r == true, "impl test 10.2 failed";
  r := ArrayWithOddSum([5, 5]);
  expect r == false, "impl test 10.3 failed";
  r := ArrayWithOddSum([4, 4]);
  expect r == false, "impl test 10.4 failed";

  // Test 11
  r := ArrayWithOddSum([1, 3, 5, 7, 9, 11, 13]);
  expect r == true, "impl test 11.1 failed";

  // Test 12
  r := ArrayWithOddSum([2, 4, 6, 8, 10]);
  expect r == false, "impl test 12.1 failed";
  r := ArrayWithOddSum([1, 3, 5, 7, 9]);
  expect r == true, "impl test 12.2 failed";

  print "All tests passed\n";
}