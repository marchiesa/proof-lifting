method DiverseStrings(strings: seq<string>) returns (results: seq<bool>)
{
  results := [];
  var idx := 0;
  while idx < |strings|
  {
    var a := strings[idx];
    var b := new int[26];
    var j := 0;
    while j < 26
    {
      b[j] := 0;
      j := j + 1;
    }
    j := 0;
    while j < |a|
    {
      var c := a[j] as int - 97;
      if 0 <= c < 26 {
        b[c] := b[c] + 1;
      }
      j := j + 1;
    }
    var diverse := true;
    var y := 0;
    var x := 0;
    var k := 0;
    while k < 27
    {
      var val := if k < 26 then b[k] else 0;
      if val > 1 {
        diverse := false;
        break;
      }
      if y == 0 && val == 1 {
        y := 1;
      }
      if y == 1 && val == 0 {
        x := 1;
        y := 0;
      }
      if x == 1 && val >= 1 {
        diverse := false;
        break;
      }
      k := k + 1;
    }
    results := results + [diverse];
    idx := idx + 1;
  }
}

method Main()
{
  // Test 1
  var r1 := DiverseStrings(["fced", "xyz", "r", "dabcef", "az", "aa", "bad", "babc"]);
  expect r1 == [true, true, true, true, false, false, false, false], "Test 1 failed";

  // Test 2
  var r2 := DiverseStrings([
    "ops", "test", "yes", "no", "ac", "bc", "cb", "z", "a", "q",
    "r", "u", "qq", "op", "po", "xu", "ux", "xy", "yx", "a",
    "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "bcdefg", "cdefg", "defg", "efgd",
    "efef", "abacaba", "abz", "aoi", "ioi", "codeforces", "klmn", "nmlk", "kln", "klmnl",
    "kmn", "kklmn", "klmnn", "aklkmn"
  ]);
  expect r2 == [
    false, false, false, true, false, true, true, true, true, true,
    true, true, false, true, true, false, false, true, true, true,
    true, true, true, true, true, true, true, true, true, true,
    false, false, false, false, false, false, true, true, false, false,
    false, false, false, false
  ], "Test 2 failed";

  // Test 3
  var r3 := DiverseStrings(["f"]);
  expect r3 == [true], "Test 3 failed";

  // Test 4
  var r4 := DiverseStrings(["shohrukh"]);
  expect r4 == [false], "Test 4 failed";

  // Test 5: 69 copies of "abc", all true
  var input5: seq<string> := [];
  var expected5: seq<bool> := [];
  var i := 0;
  while i < 69
  {
    input5 := input5 + ["abc"];
    expected5 := expected5 + [true];
    i := i + 1;
  }
  var r5 := DiverseStrings(input5);
  expect r5 == expected5, "Test 5 failed";

  // Test 6
  var r6 := DiverseStrings(["shohruk"]);
  expect r6 == [false], "Test 6 failed";

  // Test 7
  var r7 := DiverseStrings(["shohru"]);
  expect r7 == [false], "Test 7 failed";

  // Test 8
  var r8 := DiverseStrings(["shohr"]);
  expect r8 == [false], "Test 8 failed";

  // Test 9
  var r9 := DiverseStrings(["shoh"]);
  expect r9 == [false], "Test 9 failed";

  // Test 10
  var r10 := DiverseStrings(["sho"]);
  expect r10 == [false], "Test 10 failed";

  // Test 11
  var r11 := DiverseStrings(["shh"]);
  expect r11 == [false], "Test 11 failed";

  // Test 12
  var r12 := DiverseStrings(["shhh"]);
  expect r12 == [false], "Test 12 failed";

  // Test 13
  var r13 := DiverseStrings(["shhhh"]);
  expect r13 == [false], "Test 13 failed";

  // Test 14
  var r14 := DiverseStrings(["soo"]);
  expect r14 == [false], "Test 14 failed";

  // Test 15
  var r15 := DiverseStrings(["aadde"]);
  expect r15 == [false], "Test 15 failed";

  // Test 16
  var r16 := DiverseStrings(["sooo"]);
  expect r16 == [false], "Test 16 failed";

  // Test 17
  var r17 := DiverseStrings(["sdfalusdbfja"]);
  expect r17 == [false], "Test 17 failed";

  // Test 18
  var r18 := DiverseStrings(["abcxyz"]);
  expect r18 == [false], "Test 18 failed";

  // Test 19
  var r19 := DiverseStrings(["aaaab"]);
  expect r19 == [false], "Test 19 failed";

  // Test 20
  var r20 := DiverseStrings(["bcef"]);
  expect r20 == [false], "Test 20 failed";

  print "All tests passed\n";
}