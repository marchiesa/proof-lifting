predicate IsGoodString(s: seq<char>)
{
  (forall i | 0 <= i < |s| :: s[i] == 'a' || s[i] == 'b') &&
  (forall i | 0 <= i < |s| - 1 :: s[i] != s[i+1])
}

predicate GoodStringWithCounts(na: int, nb: int)
{
  na >= 0 && nb >= 0 && na - nb <= 1 && nb - na <= 1
}

predicate AchievableLength(len: int, a: int, b: int, c: int)
{
  a >= 0 && b >= 0 && c >= 0 &&
  exists pa | 0 <= pa <= a ::
    exists pb | 0 <= pb <= b ::
      exists pc | 0 <= pc <= c ::
        GoodStringWithCounts(pa + pc, pb + pc) &&
        pa + pb + 2 * pc == len
}

method AnotherOneBitesTheDust(a: int, b: int, c: int) returns (maxLen: int)
  requires a >= 0 && b >= 0 && c >= 0
  ensures AchievableLength(maxLen, a, b, c)
  ensures forall n | maxLen < n <= a + b + 2 * c :: !AchievableLength(n, a, b, c)
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

  // === SPEC POSITIVE TESTS ===
  // AchievableLength(correct_output, a, b, c) should be true
  expect AchievableLength(4, 1, 1, 1), "spec positive 1";
  expect AchievableLength(7, 2, 1, 2), "spec positive 2";
  expect AchievableLength(11, 3, 5, 2), "spec positive 3";
  expect AchievableLength(6, 2, 2, 1), "spec positive 4";
  // Test 5 skipped (values too large for bounded quantifier enumeration)
  expect AchievableLength(9, 3, 1, 3), "spec positive 6";
  expect AchievableLength(10, 2, 2, 3), "spec positive 7";
  expect AchievableLength(10, 1, 1, 4), "spec positive 8";
  expect AchievableLength(6, 1, 1, 2), "spec positive 9";
  expect AchievableLength(5, 1, 2, 1), "spec positive 10";

  // === SPEC NEGATIVE TESTS ===
  // AchievableLength(wrong_output, a, b, c) should be false
  expect !AchievableLength(5, 1, 1, 1), "spec negative 1";
  expect !AchievableLength(8, 2, 1, 2), "spec negative 2";
  expect !AchievableLength(12, 3, 5, 2), "spec negative 3";
  expect !AchievableLength(7, 2, 2, 1), "spec negative 4";
  // Test 5 skipped (values too large for bounded quantifier enumeration)
  expect !AchievableLength(10, 3, 1, 3), "spec negative 6";
  expect !AchievableLength(11, 2, 2, 3), "spec negative 7";
  expect !AchievableLength(11, 1, 1, 4), "spec negative 8";
  expect !AchievableLength(7, 1, 1, 2), "spec negative 9";
  expect !AchievableLength(6, 1, 2, 1), "spec negative 10";

  // === IMPLEMENTATION TESTS ===
  result := AnotherOneBitesTheDust(1, 1, 1);
  expect result == 4, "impl test 1 failed";

  result := AnotherOneBitesTheDust(2, 1, 2);
  expect result == 7, "impl test 2 failed";

  result := AnotherOneBitesTheDust(3, 5, 2);
  expect result == 11, "impl test 3 failed";

  result := AnotherOneBitesTheDust(2, 2, 1);
  expect result == 6, "impl test 4 failed";

  result := AnotherOneBitesTheDust(1000000000, 1000000000, 1000000000);
  expect result == 4000000000, "impl test 5 failed";

  result := AnotherOneBitesTheDust(3, 1, 3);
  expect result == 9, "impl test 6 failed";

  result := AnotherOneBitesTheDust(2, 2, 3);
  expect result == 10, "impl test 7 failed";

  result := AnotherOneBitesTheDust(1, 1, 4);
  expect result == 10, "impl test 8 failed";

  result := AnotherOneBitesTheDust(1, 1, 2);
  expect result == 6, "impl test 9 failed";

  result := AnotherOneBitesTheDust(1, 2, 1);
  expect result == 5, "impl test 10 failed";

  print "All tests passed\n";
}