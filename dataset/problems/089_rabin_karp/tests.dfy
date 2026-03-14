// Rabin-Karp Pattern Matching -- Runtime spec tests

// The spec:
//   ensures forall k :: 0 <= k < |positions| ==> 0 <= positions[k] <= |text| - |pattern|
// We test this postcondition and match verification.

method CheckPositionsInRange(positions: seq<int>, textLen: int, patLen: int) returns (ok: bool)
{
  var k := 0;
  while k < |positions|
  {
    if positions[k] < 0 || positions[k] > textLen - patLen { return false; }
    k := k + 1;
  }
  return true;
}

// Verify that at each reported position, the text actually matches the pattern
method VerifyMatches(text: seq<int>, pattern: seq<int>, positions: seq<int>) returns (ok: bool)
  requires |pattern| > 0
  requires |pattern| <= |text|
{
  var k := 0;
  while k < |positions|
  {
    if positions[k] < 0 || positions[k] > |text| - |pattern| { return false; }
    var j := 0;
    while j < |pattern|
    {
      if text[positions[k] + j] != pattern[j] { return false; }
      j := j + 1;
    }
    k := k + 1;
  }
  return true;
}

// Brute-force pattern match to find all positions
method BruteForceMatch(text: seq<int>, pattern: seq<int>) returns (positions: seq<int>)
  requires |pattern| > 0
  requires |pattern| <= |text|
{
  positions := [];
  var i := 0;
  while i <= |text| - |pattern|
  {
    var isMatch := true;
    var j := 0;
    while j < |pattern|
    {
      if text[i + j] != pattern[j] { isMatch := false; break; }
      j := j + 1;
    }
    if isMatch { positions := positions + [i]; }
    i := i + 1;
  }
}

method Main()
{
  // Test CheckPositionsInRange: valid positions
  var r := CheckPositionsInRange([1, 3], 5, 2);
  expect r, "Positions [1,3] in range for text=5, pat=2";

  r := CheckPositionsInRange([0], 3, 3);
  expect r, "Position [0] in range for text=3, pat=3";

  r := CheckPositionsInRange([], 5, 2);
  expect r, "Empty positions always in range";

  // Invalid: position out of range
  r := CheckPositionsInRange([4], 5, 2);
  expect !r, "Position 4 out of range for text=5, pat=2 (max=3)";

  r := CheckPositionsInRange([-1], 5, 2);
  expect !r, "Negative position out of range";

  r := CheckPositionsInRange([0, 5], 5, 2);
  expect !r, "Position 5 out of range for text=5, pat=2";

  // Test VerifyMatches
  var r2 := VerifyMatches([1, 2, 3, 2, 3], [2, 3], [1, 3]);
  expect r2, "Positions [1,3] are real matches for pat [2,3] in [1,2,3,2,3]";

  r2 := VerifyMatches([1, 2, 3, 2, 3], [2, 3], [0]);
  expect !r2, "Position [0] is not a match for [2,3] at start of [1,2,3,2,3]";

  // Test brute force matcher
  var pos := BruteForceMatch([1, 2, 3, 2, 3], [2, 3]);
  expect |pos| == 2, "Pattern [2,3] appears 2 times in [1,2,3,2,3]";
  r := CheckPositionsInRange(pos, 5, 2);
  expect r, "Brute force positions should be in range";
  r2 := VerifyMatches([1, 2, 3, 2, 3], [2, 3], pos);
  expect r2, "Brute force matches should be valid";

  // Test: no match
  pos := BruteForceMatch([1, 2, 3], [4, 5]);
  expect |pos| == 0, "No matches for [4,5] in [1,2,3]";

  // Test: whole text is pattern
  pos := BruteForceMatch([1, 2, 3], [1, 2, 3]);
  expect |pos| == 1, "Whole text matches pattern once";

  // Test: overlapping matches
  pos := BruteForceMatch([1, 1, 1, 1], [1, 1]);
  expect |pos| == 3, "Pattern [1,1] in [1,1,1,1] appears 3 times";

  print "All spec tests passed\n";
}
