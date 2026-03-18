function BobEncode(a: string): string
  requires |a| >= 2
  decreases |a|
{
  if |a| == 2 then a
  else a[0..2] + BobEncode(a[1..])
}

method ShortSubstrings(b: string) returns (a: string)
  requires |b| >= 2
  requires |b| % 2 == 0
  ensures |a| >= 2
  ensures BobEncode(a) == b
{
  a := "";
  var i := 1;
  while i < |b|
  {
    a := a + [b[i]];
    i := i + 2;
  }
  a := [b[0]] + a;
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // ensures: BobEncode(a) == b, where b is input and a is output
  // Testing: BobEncode(correct_output) == input

  // Test 1: "abbaac" -> "abac"
  expect BobEncode("abac") == "abbaac", "spec positive 1";
  // Test 1: "ac" -> "ac"
  expect BobEncode("ac") == "ac", "spec positive 2";
  // Test 1: "bccddaaf" -> "bcdaf"
  expect BobEncode("bcdaf") == "bccddaaf", "spec positive 3";
  // Test 1: "zzzzzzzzzz" -> "zzzzzz"
  expect BobEncode("zzzzzz") == "zzzzzzzzzz", "spec positive 4";
  // Test 2: "assaad" -> "asad"
  expect BobEncode("asad") == "assaad", "spec positive 5";
  // Test 4: "saallaammddookkhhj" -> "salamdokhj"
  expect BobEncode("salamdokhj") == "saallaammddookkhhj", "spec positive 6";
  // Test 8: "aaaa" -> "aaa"
  expect BobEncode("aaa") == "aaaa", "spec positive 7";

  // === SPEC NEGATIVE TESTS ===
  // Testing: BobEncode(wrong_output) != input

  // Negative 1: input="zzzzzzzzzz", wrong="zzzzzz WRONG"
  expect BobEncode("zzzzzz WRONG") != "zzzzzzzzzz", "spec negative 1";
  // Negative 2: input="assaad", wrong="asad WRONG"
  expect BobEncode("asad WRONG") != "assaad", "spec negative 2";
  // Negative 4: input="saallaammddookkhhj", wrong="salamdokhj WRONG"
  expect BobEncode("salamdokhj WRONG") != "saallaammddookkhhj", "spec negative 4";
  // Negative 7: input="ac", wrong="ac WRONG"
  expect BobEncode("ac WRONG") != "ac", "spec negative 7";
  // Negative 8: input="aaaa", wrong="aaa WRONG"
  expect BobEncode("aaa WRONG") != "aaaa", "spec negative 8";

  // === IMPLEMENTATION TESTS ===
  var r1 := ShortSubstrings("abbaac");
  expect r1 == "abac", "impl test 1 failed";

  var r2 := ShortSubstrings("ac");
  expect r2 == "ac", "impl test 2 failed";

  var r3 := ShortSubstrings("bccddaaf");
  expect r3 == "bcdaf", "impl test 3 failed";

  var r4 := ShortSubstrings("zzzzzzzzzz");
  expect r4 == "zzzzzz", "impl test 4 failed";

  var r5 := ShortSubstrings("assaad");
  expect r5 == "asad", "impl test 5 failed";

  var r6 := ShortSubstrings("saallaammddookkhhj");
  expect r6 == "salamdokhj", "impl test 6 failed";

  var r7 := ShortSubstrings("aaaa");
  expect r7 == "aaa", "impl test 7 failed";

  print "All tests passed\n";
}