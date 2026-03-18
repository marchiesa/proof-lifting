method LoveA(s: string) returns (result: int)
{
  var count := 0;
  var i := 0;
  while i < |s|
  {
    if s[i] == 'a' {
      count := count + 1;
    }
    i := i + 1;
  }
  var candidate := 2 * count - 1;
  if |s| < candidate {
    result := |s|;
  } else {
    result := candidate;
  }
}

method Main()
{
  var r1 := LoveA("xaxxxxa");
  expect r1 == 3, "Test 1 failed";

  var r2 := LoveA("aaabaa");
  expect r2 == 6, "Test 2 failed";

  var r3 := LoveA("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
  expect r3 == 50, "Test 3 failed";

  var r4 := LoveA("ababababababababababababababababababababababababav");
  expect r4 == 49, "Test 4 failed";

  var r5 := LoveA("abababababababababababababababababababababababava");
  expect r5 == 49, "Test 5 failed";

  var r6 := LoveA("abababababababababababababababababababababababavv");
  expect r6 == 47, "Test 6 failed";

  var r7 := LoveA("a");
  expect r7 == 1, "Test 7 failed";

  var r8 := LoveA("ap");
  expect r8 == 1, "Test 8 failed";

  var r9 := LoveA("dya");
  expect r9 == 1, "Test 9 failed";

  var r10 := LoveA("qyax");
  expect r10 == 1, "Test 10 failed";

  var r11 := LoveA("ahaos");
  expect r11 == 3, "Test 11 failed";

  var r12 := LoveA("caidsucitzpblhucxnzcdupstfoourafborgyqwvaymdk");
  expect r12 == 5, "Test 12 failed";

  var r13 := LoveA("wqufdkunalpjjmeolduzppvzabhytailycojjhnsykfhim");
  expect r13 == 5, "Test 13 failed";

  var r14 := LoveA("qfggoxltgxqqirqazusxblbhhuajrjrsuojnwvdnzwymhjx");
  expect r14 == 3, "Test 14 failed";

  var r15 := LoveA("kvujzkexnkqygxalmlpupghpqqsvqsabpbgrhmwixfroghpm");
  expect r15 == 3, "Test 15 failed";

  var r16 := LoveA("ckhklxvduyregcmxabkrbcnxxjlgoaiikpbvuamdvrksefigx");
  expect r16 == 5, "Test 16 failed";

  var r17 := LoveA("yqahbyyoxltryqdmvenemaqnbakglgqolxnaifnqtoclnnqiab");
  expect r17 == 9, "Test 17 failed";

  var r18 := LoveA("ass");
  expect r18 == 1, "Test 18 failed";

  var r19 := LoveA("xaxax");
  expect r19 == 3, "Test 19 failed";

  print "All tests passed\n";
}