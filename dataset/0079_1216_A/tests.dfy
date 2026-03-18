predicate ValidAB(s: seq<char>)
{
  forall i | 0 <= i < |s| :: s[i] == 'a' || s[i] == 'b'
}

function CountChar(s: seq<char>, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountChar(s[..|s|-1], c) + (if s[|s|-1] == c then 1 else 0)
}

predicate BalancedPrefixes(s: seq<char>)
{
  forall k | 1 <= k <= |s| / 2 :: CountChar(s[..2 * k], 'a') == CountChar(s[..2 * k], 'b')
}

function HammingDist(s: seq<char>, t: seq<char>): int
  requires |s| == |t|
  decreases |s|
{
  if |s| == 0 then 0
  else HammingDist(s[..|s|-1], t[..|t|-1]) + (if s[|s|-1] != t[|t|-1] then 1 else 0)
}

function CountBadPairs(s: seq<char>): int
  requires |s| % 2 == 0
  decreases |s|
{
  if |s| == 0 then 0
  else CountBadPairs(s[..|s|-2]) + (if s[|s|-2] == s[|s|-1] then 1 else 0)
}

method Prefixes(s: seq<char>) returns (ops: int, result: seq<char>)
  requires |s| % 2 == 0
  requires ValidAB(s)
  ensures |result| == |s|
  ensures ValidAB(result)
  ensures BalancedPrefixes(result)
  ensures ops == HammingDist(s, result)
  ensures ops == CountBadPairs(s)
{
  ops := 0;
  result := [];
  var i := 0;
  while i < |s|
  {
    if s[i] == s[i + 1] {
      result := result + ['a', 'b'];
      ops := ops + 1;
    } else {
      result := result + [s[i], s[i + 1]];
    }
    i := i + 2;
  }
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Each ensures predicate tested with small inputs and correct outputs.

  // Spec positive 1: s="aa", ops=1, result="ab" (from test 3)
  var sp1s: seq<char> := ['a', 'a'];
  var sp1r: seq<char> := ['a', 'b'];
  expect |sp1r| == |sp1s|, "spec positive 1: length";
  expect ValidAB(sp1r), "spec positive 1: ValidAB";
  expect BalancedPrefixes(sp1r), "spec positive 1: BalancedPrefixes";
  expect 1 == HammingDist(sp1s, sp1r), "spec positive 1: HammingDist";
  expect 1 == CountBadPairs(sp1s), "spec positive 1: CountBadPairs";

  // Spec positive 2: s="ab", ops=0, result="ab" (from test 2 scaled to len 2)
  var sp2s: seq<char> := ['a', 'b'];
  var sp2r: seq<char> := ['a', 'b'];
  expect |sp2r| == |sp2s|, "spec positive 2: length";
  expect ValidAB(sp2r), "spec positive 2: ValidAB";
  expect BalancedPrefixes(sp2r), "spec positive 2: BalancedPrefixes";
  expect 0 == HammingDist(sp2s, sp2r), "spec positive 2: HammingDist";
  expect 0 == CountBadPairs(sp2s), "spec positive 2: CountBadPairs";

  // Spec positive 3: s="ba", ops=0, result="ba" (from test 4 scaled to len 2)
  var sp3s: seq<char> := ['b', 'a'];
  var sp3r: seq<char> := ['b', 'a'];
  expect |sp3r| == |sp3s|, "spec positive 3: length";
  expect ValidAB(sp3r), "spec positive 3: ValidAB";
  expect BalancedPrefixes(sp3r), "spec positive 3: BalancedPrefixes";
  expect 0 == HammingDist(sp3s, sp3r), "spec positive 3: HammingDist";
  expect 0 == CountBadPairs(sp3s), "spec positive 3: CountBadPairs";

  // Spec positive 4: s="bb", ops=1, result="ab" (from test 1 scaled to len 2)
  var sp4s: seq<char> := ['b', 'b'];
  var sp4r: seq<char> := ['a', 'b'];
  expect |sp4r| == |sp4s|, "spec positive 4: length";
  expect ValidAB(sp4r), "spec positive 4: ValidAB";
  expect BalancedPrefixes(sp4r), "spec positive 4: BalancedPrefixes";
  expect 1 == HammingDist(sp4s, sp4r), "spec positive 4: HammingDist";
  expect 1 == CountBadPairs(sp4s), "spec positive 4: CountBadPairs";

  // Spec positive 5: s="bbbb", ops=2, result="abab" (test 1, len 4)
  var sp5s: seq<char> := ['b', 'b', 'b', 'b'];
  var sp5r: seq<char> := ['a', 'b', 'a', 'b'];
  expect |sp5r| == |sp5s|, "spec positive 5: length";
  expect ValidAB(sp5r), "spec positive 5: ValidAB";
  expect BalancedPrefixes(sp5r), "spec positive 5: BalancedPrefixes";
  expect 2 == HammingDist(sp5s, sp5r), "spec positive 5: HammingDist";
  expect 2 == CountBadPairs(sp5s), "spec positive 5: CountBadPairs";

  // Spec positive 6: s="abab", ops=0, result="abab" (test 2 scaled to len 4)
  var sp6s: seq<char> := ['a', 'b', 'a', 'b'];
  var sp6r: seq<char> := ['a', 'b', 'a', 'b'];
  expect |sp6r| == |sp6s|, "spec positive 6: length";
  expect ValidAB(sp6r), "spec positive 6: ValidAB";
  expect BalancedPrefixes(sp6r), "spec positive 6: BalancedPrefixes";
  expect 0 == HammingDist(sp6s, sp6r), "spec positive 6: HammingDist";
  expect 0 == CountBadPairs(sp6s), "spec positive 6: CountBadPairs";

  // ===== SPEC NEGATIVE TESTS =====
  // Wrong ops values must be rejected by HammingDist/CountBadPairs ensures.

  // Spec negative 1: s="bb", wrong_ops=2 (scaled from neg 1: bbbb, wrong=3)
  expect 2 != HammingDist(['b', 'b'], ['a', 'b']), "spec negative 1: HammingDist";
  expect 2 != CountBadPairs(['b', 'b']), "spec negative 1: CountBadPairs";

  // Spec negative 2: s="ab", wrong_ops=1 (scaled from neg 2: ababab, wrong=1)
  expect 1 != HammingDist(['a', 'b'], ['a', 'b']), "spec negative 2: HammingDist";
  expect 1 != CountBadPairs(['a', 'b']), "spec negative 2: CountBadPairs";

  // Spec negative 3: s="aa", wrong_ops=2 (from neg 3: aa, wrong=2)
  expect 2 != HammingDist(['a', 'a'], ['a', 'b']), "spec negative 3: HammingDist";
  expect 2 != CountBadPairs(['a', 'a']), "spec negative 3: CountBadPairs";

  // Spec negative 4: s="ba", wrong_ops=1 (scaled from neg 4: bbbbba, wrong=3)
  expect 1 != HammingDist(['b', 'a'], ['b', 'a']), "spec negative 4: HammingDist";
  expect 1 != CountBadPairs(['b', 'a']), "spec negative 4: CountBadPairs";

  // Spec negative 5: s="bbbb", wrong_ops=3 (neg 1: bbbb, wrong=3)
  expect 3 != HammingDist(['b', 'b', 'b', 'b'], ['a', 'b', 'a', 'b']), "spec negative 5: HammingDist";
  expect 3 != CountBadPairs(['b', 'b', 'b', 'b']), "spec negative 5: CountBadPairs";

  // Spec negative 6: s="abab", wrong_ops=1 (scaled neg 2 to len 4)
  expect 1 != HammingDist(['a', 'b', 'a', 'b'], ['a', 'b', 'a', 'b']), "spec negative 6: HammingDist";
  expect 1 != CountBadPairs(['a', 'b', 'a', 'b']), "spec negative 6: CountBadPairs";

  // ===== IMPLEMENTATION TESTS =====

  // Impl test 1: bbbb -> ops=2, result=abab
  var ops1, res1 := Prefixes(['b', 'b', 'b', 'b']);
  expect ops1 == 2, "impl test 1: ops";
  expect res1 == ['a', 'b', 'a', 'b'], "impl test 1: result";

  // Impl test 2: ababab -> ops=0, result=ababab
  var ops2, res2 := Prefixes(['a', 'b', 'a', 'b', 'a', 'b']);
  expect ops2 == 0, "impl test 2: ops";
  expect res2 == ['a', 'b', 'a', 'b', 'a', 'b'], "impl test 2: result";

  // Impl test 3: aa -> ops=1, result=ab
  var ops3, res3 := Prefixes(['a', 'a']);
  expect ops3 == 1, "impl test 3: ops";
  expect res3 == ['a', 'b'], "impl test 3: result";

  // Impl test 4: bbbbba -> ops=2, result=ababba
  var ops4, res4 := Prefixes(['b', 'b', 'b', 'b', 'b', 'a']);
  expect ops4 == 2, "impl test 4: ops";
  expect res4 == ['a', 'b', 'a', 'b', 'b', 'a'], "impl test 4: result";

  // Impl test 5: bbbabbba -> ops=2, result=abbaabba
  var ops5, res5 := Prefixes(['b', 'b', 'b', 'a', 'b', 'b', 'b', 'a']);
  expect ops5 == 2, "impl test 5: ops";
  expect res5 == ['a', 'b', 'b', 'a', 'a', 'b', 'b', 'a'], "impl test 5: result";

  // Impl test 6: bbabbbaa -> ops=3, result=abababab
  var ops6, res6 := Prefixes(['b', 'b', 'a', 'b', 'b', 'b', 'a', 'a']);
  expect ops6 == 3, "impl test 6: ops";
  expect res6 == ['a', 'b', 'a', 'b', 'a', 'b', 'a', 'b'], "impl test 6: result";

  print "All tests passed\n";
}