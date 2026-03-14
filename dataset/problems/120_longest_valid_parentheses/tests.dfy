// Longest Valid Parentheses -- Test cases
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

method {:axiom} LongestValidParens(s: seq<int>) returns (maxLen: int)
  requires forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1
  ensures maxLen >= 0
  ensures maxLen <= |s|
  ensures exists lo :: 0 <= lo <= |s| - maxLen && ValidParens(s, lo, lo + maxLen)

method TestEmpty() {
  var r := LongestValidParens([]);
  assert r == 0;
}

method TestSimplePair() {
  // "()" = [1, 0]
  var r := LongestValidParens([1, 0]);
}

method TestNested() {
  // "(())" = [1, 1, 0, 0]
  var r := LongestValidParens([1, 1, 0, 0]);
}
