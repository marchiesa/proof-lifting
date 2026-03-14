// Word Break -- Runtime spec tests

// Bounded InDict for runtime
function InDictBounded(dict: seq<seq<int>>, word: seq<int>): bool
{
  if |dict| == 0 then false
  else dict[0] == word || InDictBounded(dict[1..], word)
}

// Iterative breakable check: dp[i] = can s[0..i] be broken into dict words?
method BreakableCheck(s: seq<int>, dict: seq<seq<int>>) returns (result: bool)
{
  var dp := new bool[|s| + 1];
  dp[0] := true;
  var i := 1;
  while i <= |s|
    invariant 0 <= i <= |s| + 1
  {
    dp[i] := false;
    var k := 0;
    while k < i
      invariant 0 <= k <= i
    {
      if dp[k] && InDictBounded(dict, s[k..i]) {
        dp[i] := true;
      }
      k := k + 1;
    }
    i := i + 1;
  }
  result := dp[|s|];
}

method Main()
{
  // InDictBounded tests
  var dict := [[1, 2], [3, 4]];
  expect InDictBounded(dict, [1, 2]), "[1,2] is in dict";
  expect InDictBounded(dict, [3, 4]), "[3,4] is in dict";
  expect !InDictBounded(dict, [1, 3]), "[1,3] is not in dict";
  expect !InDictBounded([], [1, 2]), "Nothing in empty dict";

  // BreakableCheck: empty string
  var r0 := BreakableCheck([], [[1]]);
  expect r0, "Empty string is always breakable";

  // BreakableCheck: single word match
  var r1 := BreakableCheck([1, 2], [[1, 2]]);
  expect r1, "[1,2] breakable with dict {[1,2]}";

  // BreakableCheck: two word match
  var r2 := BreakableCheck([1, 2, 1, 2], [[1, 2]]);
  expect r2, "[1,2,1,2] breakable with dict {[1,2]}";

  // BreakableCheck: two different words
  var r3 := BreakableCheck([1, 2, 3, 4], [[1, 2], [3, 4]]);
  expect r3, "[1,2,3,4] breakable with dict {[1,2],[3,4]}";

  // BreakableCheck: not breakable
  var r4 := BreakableCheck([1, 2, 3], [[1, 2]]);
  expect !r4, "[1,2,3] not breakable with dict {[1,2]}";

  var r5 := BreakableCheck([1, 3], [[1, 2]]);
  expect !r5, "[1,3] not breakable with dict {[1,2]}";

  // BreakableCheck: not in dict at all
  var r6 := BreakableCheck([1, 2], [[3, 4]]);
  expect !r6, "[1,2] not breakable with dict {[3,4]}";

  // BreakableCheck: overlapping words
  var r7 := BreakableCheck([1, 2, 3], [[1, 2, 3], [1, 2], [3]]);
  expect r7, "[1,2,3] breakable multiple ways";

  // BreakableCheck: single char words
  var r8 := BreakableCheck([1, 2, 3], [[1], [2], [3]]);
  expect r8, "[1,2,3] breakable with single-char dict";

  print "All spec tests passed\n";
}
