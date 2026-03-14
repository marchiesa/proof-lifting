// Longest Valid Parentheses -- Reference solution with invariants

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

lemma EmptyIsValid(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures ValidParens(s, i, i)
{
}

method LongestValidParens(s: seq<int>) returns (maxLen: int)
  requires forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1
  ensures maxLen >= 0
  ensures maxLen <= |s|
  ensures exists lo :: 0 <= lo <= |s| - maxLen && ValidParens(s, lo, lo + maxLen)
{
  maxLen := 0;
  ghost var bestStart := 0;
  EmptyIsValid(s, 0);
  // O(n^3) brute force
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= maxLen <= |s|
    invariant 0 <= bestStart <= |s| - maxLen
    invariant ValidParens(s, bestStart, bestStart + maxLen)
    decreases |s| - i
  {
    var j := i;
    while j <= |s|
      invariant i <= j <= |s| + 1
      invariant 0 <= maxLen <= |s|
      invariant 0 <= bestStart <= |s| - maxLen
      invariant ValidParens(s, bestStart, bestStart + maxLen)
      decreases |s| + 1 - j
    {
      if j > i && j <= |s| && ValidParens(s, i, j) && j - i > maxLen {
        maxLen := j - i;
        bestStart := i;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
