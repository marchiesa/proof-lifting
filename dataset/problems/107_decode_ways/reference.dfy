// Decode Ways -- Reference solution with invariants

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

method DecodeWays(s: seq<int>) returns (result: nat)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i] <= 9
  ensures result == NumDecodings(s, |s|)
{
  if |s| == 1 {
    result := if ValidDigit(s[0]) then 1 else 0;
    return;
  }
  var prev2: nat := 1;
  var prev1: nat := if ValidDigit(s[0]) then 1 else 0;
  var i := 2;
  while i <= |s|
    invariant 2 <= i <= |s| + 1
    invariant prev2 == NumDecodings(s, i - 2)
    invariant prev1 == NumDecodings(s, i - 1)
    decreases |s| + 1 - i
  {
    var curr: nat := 0;
    if ValidDigit(s[i-1]) {
      curr := curr + prev1;
    }
    if ValidTwoDigit(s[i-2], s[i-1]) {
      curr := curr + prev2;
    }
    prev2 := prev1;
    prev1 := curr;
    i := i + 1;
  }
  result := prev1;
}
