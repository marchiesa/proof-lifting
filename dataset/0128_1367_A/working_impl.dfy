method ShortSubstrings(b: string) returns (a: string)
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
  // From Test 1 / repeated across Tests 3,5,6,7
  var r1 := ShortSubstrings("abbaac");
  expect r1 == "abac", "Test abbaac failed";

  var r2 := ShortSubstrings("ac");
  expect r2 == "ac", "Test ac failed";

  var r3 := ShortSubstrings("bccddaaf");
  expect r3 == "bcdaf", "Test bccddaaf failed";

  var r4 := ShortSubstrings("zzzzzzzzzz");
  expect r4 == "zzzzzz", "Test zzzzzzzzzz failed";

  // From Test 2
  var r5 := ShortSubstrings("assaad");
  expect r5 == "asad", "Test assaad failed";

  // From Test 4
  var r6 := ShortSubstrings("saallaammddookkhhj");
  expect r6 == "salamdokhj", "Test saallaammddookkhhj failed";

  // From Test 8
  var r7 := ShortSubstrings("aaaa");
  expect r7 == "aaa", "Test aaaa failed";

  print "All tests passed\n";
}