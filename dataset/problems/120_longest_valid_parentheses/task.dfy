// Longest Valid Parentheses
// Task: Add loop invariants so that Dafny can verify this program.
// Given a string of '(' (encoded as 1) and ')' (encoded as 0),
// find the length of the longest valid parentheses substring.

function Balance(s: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |s|
  decreases hi - lo
{
  if lo == hi then 0
  else (if s[lo] == 1 then 1 else -1) + Balance(s, lo + 1, hi)
}

predicate BalanceNeverNeg(s: seq<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= |s|
{
  forall k :: lo <= k <= hi ==> Balance(s, lo, k) >= 0
}

predicate ValidParens(s: seq<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= |s|
{
  BalanceNeverNeg(s, lo, hi) && Balance(s, lo, hi) == 0
}

method LongestValidParens(s: seq<int>) returns (maxLen: int)
  requires forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1
  ensures maxLen >= 0
  ensures maxLen <= |s|
  ensures exists lo :: 0 <= lo <= |s| - maxLen && ValidParens(s, lo, lo + maxLen)
{
  maxLen := 0;
  // O(n^3) brute force
  var i := 0;
  while i < |s|
  {
    var j := i;
    while j <= |s|
    {
      if j > i && j <= |s| && ValidParens(s, i, j) && j - i > maxLen {
        maxLen := j - i;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
