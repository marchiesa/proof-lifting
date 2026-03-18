method SplitIntoDigits(n: int) returns (k: int, digits: seq<int>)
{
  k := n;
  digits := seq(n, _ => 1);
}

method Main()
{
  var k: int;
  var digits: seq<int>;

  // Test 1: n=1
  k, digits := SplitIntoDigits(1);
  expect k == 1, "Test 1: k mismatch";
  expect digits == seq(1, _ => 1), "Test 1: digits mismatch";

  // Test 2: n=4
  k, digits := SplitIntoDigits(4);
  expect k == 4, "Test 2: k mismatch";
  expect digits == seq(4, _ => 1), "Test 2: digits mismatch";

  // Test 3: n=27
  k, digits := SplitIntoDigits(27);
  expect k == 27, "Test 3: k mismatch";
  expect digits == seq(27, _ => 1), "Test 3: digits mismatch";

  // Test 4: n=1000
  k, digits := SplitIntoDigits(1000);
  expect k == 1000, "Test 4: k mismatch";
  expect digits == seq(1000, _ => 1), "Test 4: digits mismatch";

  // Test 5: n=239
  k, digits := SplitIntoDigits(239);
  expect k == 239, "Test 5: k mismatch";
  expect digits == seq(239, _ => 1), "Test 5: digits mismatch";

  // Test 6: n=997
  k, digits := SplitIntoDigits(997);
  expect k == 997, "Test 6: k mismatch";
  expect digits == seq(997, _ => 1), "Test 6: digits mismatch";

  // Test 7: n=998
  k, digits := SplitIntoDigits(998);
  expect k == 998, "Test 7: k mismatch";
  expect digits == seq(998, _ => 1), "Test 7: digits mismatch";

  // Test 8: n=993
  k, digits := SplitIntoDigits(993);
  expect k == 993, "Test 8: k mismatch";
  expect digits == seq(993, _ => 1), "Test 8: digits mismatch";

  // Test 9: n=988
  k, digits := SplitIntoDigits(988);
  expect k == 988, "Test 9: k mismatch";
  expect digits == seq(988, _ => 1), "Test 9: digits mismatch";

  // Test 10: n=995
  k, digits := SplitIntoDigits(995);
  expect k == 995, "Test 10: k mismatch";
  expect digits == seq(995, _ => 1), "Test 10: digits mismatch";

  // Test 11: n=996
  k, digits := SplitIntoDigits(996);
  expect k == 996, "Test 11: k mismatch";
  expect digits == seq(996, _ => 1), "Test 11: digits mismatch";

  // Test 12: n=994
  k, digits := SplitIntoDigits(994);
  expect k == 994, "Test 12: k mismatch";
  expect digits == seq(994, _ => 1), "Test 12: digits mismatch";

  // Test 13: n=992
  k, digits := SplitIntoDigits(992);
  expect k == 992, "Test 13: k mismatch";
  expect digits == seq(992, _ => 1), "Test 13: digits mismatch";

  // Test 14: n=999
  k, digits := SplitIntoDigits(999);
  expect k == 999, "Test 14: k mismatch";
  expect digits == seq(999, _ => 1), "Test 14: digits mismatch";

  // Test 15: n=191
  k, digits := SplitIntoDigits(191);
  expect k == 191, "Test 15: k mismatch";
  expect digits == seq(191, _ => 1), "Test 15: digits mismatch";

  // Test 16: n=94
  k, digits := SplitIntoDigits(94);
  expect k == 94, "Test 16: k mismatch";
  expect digits == seq(94, _ => 1), "Test 16: digits mismatch";

  // Test 17: n=57
  k, digits := SplitIntoDigits(57);
  expect k == 57, "Test 17: k mismatch";
  expect digits == seq(57, _ => 1), "Test 17: digits mismatch";

  // Test 18: n=748
  k, digits := SplitIntoDigits(748);
  expect k == 748, "Test 18: k mismatch";
  expect digits == seq(748, _ => 1), "Test 18: digits mismatch";

  // Test 19: n=485
  k, digits := SplitIntoDigits(485);
  expect k == 485, "Test 19: k mismatch";
  expect digits == seq(485, _ => 1), "Test 19: digits mismatch";

  // Test 20: n=78
  k, digits := SplitIntoDigits(78);
  expect k == 78, "Test 20: k mismatch";
  expect digits == seq(78, _ => 1), "Test 20: digits mismatch";

  print "All tests passed\n";
}