// Decode Ways -- Test cases
predicate ValidDigit(d: int) { 1 <= d && d <= 9 }
predicate ValidTwoDigit(d1: int, d2: int) { d1 * 10 + d2 >= 10 && d1 * 10 + d2 <= 26 }

function NumDecodings(s: seq<int>, n: int): nat
  requires 0 <= n <= |s|
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i] <= 9
  decreases n
{
  if n == 0 then 1
  else if n == 1 then (if ValidDigit(s[0]) then 1 else 0)
  else
    (if ValidDigit(s[n-1]) then NumDecodings(s, n-1) else 0) +
    (if ValidTwoDigit(s[n-2], s[n-1]) then NumDecodings(s, n-2) else 0)
}

method {:axiom} DecodeWays(s: seq<int>) returns (result: nat)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i] <= 9
  ensures result == NumDecodings(s, |s|)

method TestSingle() { var r := DecodeWays([1]); assert r == 1; }
method TestTwo() { var r := DecodeWays([1, 2]); }
