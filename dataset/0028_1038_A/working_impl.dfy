method LongestGoodSubsequence(s: seq<char>, k: int) returns (length: int)
{
  var upper: seq<char> := [];
  var i := 0;
  var limit := if k < 26 then k else 26;
  while i < limit
  {
    upper := upper + [('A' as int + i) as char];
    i := i + 1;
  }

  if |upper| == 0 {
    length := 0;
    return;
  }

  var counts: seq<int> := [];
  i := 0;
  while i < |upper|
  {
    var count := 0;
    var j := 0;
    while j < |s|
    {
      if s[j] == upper[i] {
        count := count + 1;
      }
      j := j + 1;
    }
    counts := counts + [count];
    i := i + 1;
  }

  var minCount := counts[0];
  i := 1;
  while i < |counts|
  {
    if counts[i] < minCount {
      minCount := counts[i];
    }
    i := i + 1;
  }

  length := minCount * k;
}

method Main()
{
  // Test 1
  var r1 := LongestGoodSubsequence("ACAABCCAB", 3);
  expect r1 == 6, "Test 1 failed";

  // Test 2
  var r2 := LongestGoodSubsequence("ABCABCABC", 4);
  expect r2 == 0, "Test 2 failed";

  // Test 3
  var r3 := LongestGoodSubsequence("A", 26);
  expect r3 == 0, "Test 3 failed";

  // Test 4
  var r4 := LongestGoodSubsequence("AAAAAAAAAAAAAAAAAAAAAA", 1);
  expect r4 == 22, "Test 4 failed";

  // Test 5
  var r5 := LongestGoodSubsequence("WEYYDIADTLCOUEG", 26);
  expect r5 == 0, "Test 5 failed";

  // Test 6
  var r6 := LongestGoodSubsequence("BA", 2);
  expect r6 == 2, "Test 6 failed";

  // Test 7
  var r7 := LongestGoodSubsequence("AABBCC", 3);
  expect r7 == 6, "Test 7 failed";

  // Test 8
  var r8 := LongestGoodSubsequence("A", 5);
  expect r8 == 0, "Test 8 failed";

  // Test 9
  var r9 := LongestGoodSubsequence("ABBBBBBBBB", 2);
  expect r9 == 2, "Test 9 failed";

  // Test 10
  var r10 := LongestGoodSubsequence("A", 1);
  expect r10 == 1, "Test 10 failed";

  // Test 11
  var r11 := LongestGoodSubsequence("ABBCCC", 3);
  expect r11 == 3, "Test 11 failed";

  // Test 12
  var r12 := LongestGoodSubsequence("AABBBBB", 2);
  expect r12 == 4, "Test 12 failed";

  // Test 13
  var r13 := LongestGoodSubsequence("ABCDEFGHIJKLMNOPQRSTUVWXYZABCDEFGHIJKLMNOPQRSTUVWXYABCDEFGHIJKLMNOPQRSTUVWXY", 26);
  expect r13 == 26, "Test 13 failed";

  // Test 14
  var r14 := LongestGoodSubsequence("AABBC", 3);
  expect r14 == 3, "Test 14 failed";

  // Test 15
  var r15 := LongestGoodSubsequence("AAC", 3);
  expect r15 == 0, "Test 15 failed";

  // Test 16
  var r16 := LongestGoodSubsequence("D", 4);
  expect r16 == 0, "Test 16 failed";

  // Test 17
  var r17 := LongestGoodSubsequence("BBB", 2);
  expect r17 == 0, "Test 17 failed";

  // Test 18
  var r18 := LongestGoodSubsequence("CBA", 3);
  expect r18 == 3, "Test 18 failed";

  // Test 19
  var r19 := LongestGoodSubsequence("ABC", 5);
  expect r19 == 0, "Test 19 failed";

  print "All tests passed\n";
}