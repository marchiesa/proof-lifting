// Count the number of 'a' characters in a string
function CountA(s: string): nat
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[|s|-1] == 'a' then 1 else 0) + CountA(s[..|s|-1])
}

predicate CanFormGoodOfLength(s: string, len: int)
{
  0 <= len <= |s| &&
  exists numA: int | 0 <= numA <= len ::
    numA <= CountA(s) &&
    len - numA + CountA(s) <= |s| &&
    2 * numA > len
}

method LoveA(s: string) returns (result: int)
  requires CountA(s) >= 1
  ensures 0 <= result <= |s|
  ensures CanFormGoodOfLength(s, result)
  ensures forall k | result < k <= |s| :: !CanFormGoodOfLength(s, k)
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
  // === SPEC POSITIVE TESTS ===
  // CanFormGoodOfLength(s, correct_output) should be true
  // Using small inputs (length 1-3) to keep bounded quantifier fast

  expect CanFormGoodOfLength("a", 1), "spec positive 1";       // from test 7
  expect CanFormGoodOfLength("ap", 1), "spec positive 2";      // from test 8
  expect CanFormGoodOfLength("dya", 1), "spec positive 3";     // from test 9
  expect CanFormGoodOfLength("aa", 2), "spec positive 4";      // scaled from test 3 (all a's -> full length)
  expect CanFormGoodOfLength("aab", 3), "spec positive 5";     // scaled from test 2 (mostly a's -> full length)
  expect CanFormGoodOfLength("aba", 3), "spec positive 6";     // scaled from test 4 (alternating -> full length)
  expect CanFormGoodOfLength("ab", 1), "spec positive 7";      // scaled from test 6 (few a's -> short good)

  // === SPEC NEGATIVE TESTS ===
  // CanFormGoodOfLength(s, wrong_output) should be false
  // Using small inputs (length 1-3) to keep bounded quantifier fast

  expect !CanFormGoodOfLength("a", 2), "spec negative 1";      // from neg 7: wrong > |s|
  expect !CanFormGoodOfLength("ap", 2), "spec negative 2";     // from neg 8: need numA>1 but only 1 'a'
  expect !CanFormGoodOfLength("dya", 2), "spec negative 3";    // from neg 9: need numA>1 but only 1 'a'
  expect !CanFormGoodOfLength("aa", 3), "spec negative 4";     // scaled neg 3: wrong > |s|
  expect !CanFormGoodOfLength("aab", 4), "spec negative 5";    // scaled neg 2: wrong > |s|
  expect !CanFormGoodOfLength("ab", 2), "spec negative 6";     // scaled neg 6: need numA>1 but only 1 'a'
  expect !CanFormGoodOfLength("aba", 4), "spec negative 7";    // scaled neg 4: wrong > |s|

  // === IMPLEMENTATION TESTS ===
  var r1 := LoveA("xaxxxxa");
  expect r1 == 3, "impl test 1 failed";

  var r2 := LoveA("aaabaa");
  expect r2 == 6, "impl test 2 failed";

  var r3 := LoveA("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
  expect r3 == 50, "impl test 3 failed";

  var r4 := LoveA("ababababababababababababababababababababababababav");
  expect r4 == 49, "impl test 4 failed";

  var r5 := LoveA("abababababababababababababababababababababababava");
  expect r5 == 49, "impl test 5 failed";

  var r6 := LoveA("abababababababababababababababababababababababavv");
  expect r6 == 47, "impl test 6 failed";

  var r7 := LoveA("a");
  expect r7 == 1, "impl test 7 failed";

  var r8 := LoveA("ap");
  expect r8 == 1, "impl test 8 failed";

  var r9 := LoveA("dya");
  expect r9 == 1, "impl test 9 failed";

  var r10 := LoveA("qyax");
  expect r10 == 1, "impl test 10 failed";

  var r11 := LoveA("ahaos");
  expect r11 == 3, "impl test 11 failed";

  var r12 := LoveA("caidsucitzpblhucxnzcdupstfoourafborgyqwvaymdk");
  expect r12 == 5, "impl test 12 failed";

  var r13 := LoveA("wqufdkunalpjjmeolduzppvzabhytailycojjhnsykfhim");
  expect r13 == 5, "impl test 13 failed";

  var r14 := LoveA("qfggoxltgxqqirqazusxblbhhuajrjrsuojnwvdnzwymhjx");
  expect r14 == 3, "impl test 14 failed";

  var r15 := LoveA("kvujzkexnkqygxalmlpupghpqqsvqsabpbgrhmwixfroghpm");
  expect r15 == 3, "impl test 15 failed";

  var r16 := LoveA("ckhklxvduyregcmxabkrbcnxxjlgoaiikpbvuamdvrksefigx");
  expect r16 == 5, "impl test 16 failed";

  var r17 := LoveA("yqahbyyoxltryqdmvenemaqnbakglgqolxnaifnqtoclnnqiab");
  expect r17 == 9, "impl test 17 failed";

  var r18 := LoveA("ass");
  expect r18 == 1, "impl test 18 failed";

  var r19 := LoveA("xaxax");
  expect r19 == 3, "impl test 19 failed";

  print "All tests passed\n";
}