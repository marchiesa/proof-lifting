method StringSimilarity(n: int, s: string) returns (w: string)
{
  var c := s[n - 1];
  w := "";
  var i := 0;
  while i < n
  {
    w := w + [c];
    i := i + 1;
  }
}

method Main()
{
  // Test 1 (t=4)
  var r1 := StringSimilarity(1, "1");
  expect r1 == "1", "Test 1a failed";

  var r2 := StringSimilarity(3, "00000");
  expect r2 == "000", "Test 1b failed";

  var r3 := StringSimilarity(4, "1110000");
  expect r3 == "0000", "Test 1c failed";

  var r4 := StringSimilarity(2, "101");
  expect r4 == "00", "Test 1d failed";

  // Test 2 (t=1)
  var r5 := StringSimilarity(7, "0000000000001");
  expect r5 == "0000000", "Test 2 failed";

  // Test 3 (t=1)
  var r6 := StringSimilarity(1, "0");
  expect r6 == "0", "Test 3 failed";

  // Test 4 (t=1)
  var r7 := StringSimilarity(2, "110");
  expect r7 == "11", "Test 4 failed";

  // Test 5 (t=1)
  var r8 := StringSimilarity(5, "000000000");
  expect r8 == "00000", "Test 5 failed";

  // Test 6 (t=1)
  var r9 := StringSimilarity(5, "111111111");
  expect r9 == "11111", "Test 6 failed";

  // Test 7 (t=2)
  var r10 := StringSimilarity(3, "01010");
  expect r10 == "000", "Test 7a failed";

  var r11 := StringSimilarity(4, "1001110");
  expect r11 == "1111", "Test 7b failed";

  // Test 8 (t=1)
  var r12 := StringSimilarity(3, "10101");
  expect r12 == "111", "Test 8 failed";

  // Test 9 (t=3)
  var r13 := StringSimilarity(1, "1");
  expect r13 == "1", "Test 9a failed";

  var r14 := StringSimilarity(2, "010");
  expect r14 == "11", "Test 9b failed";

  var r15 := StringSimilarity(3, "11100");
  expect r15 == "111", "Test 9c failed";

  // Test 10 (t=1)
  var r16 := StringSimilarity(6, "10101010101");
  expect r16 == "000000", "Test 10 failed";

  // Test 11 (t=2)
  var r17 := StringSimilarity(4, "0000000");
  expect r17 == "0000", "Test 11a failed";

  var r18 := StringSimilarity(4, "1111111");
  expect r18 == "1111", "Test 11b failed";

  // Test 12 (t=1)
  var r19 := StringSimilarity(7, "0110100110100");
  expect r19 == "0000000", "Test 12 failed";

  print "All tests passed\n";
}