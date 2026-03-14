// Word Break (DP) -- Reference solution with invariants

predicate InDict(dict: seq<seq<int>>, word: seq<int>)
{
  exists i :: 0 <= i < |dict| && dict[i] == word
}

function Breakable(s: seq<int>, dict: seq<seq<int>>, n: int): bool
  requires 0 <= n <= |s|
  decreases n
{
  if n == 0 then true
  else exists k :: 0 <= k < n && Breakable(s, dict, k) && InDict(dict, s[k..n])
}

method FindInDict(dict: seq<seq<int>>, word: seq<int>) returns (found: bool)
  ensures found <==> InDict(dict, word)
{
  found := false;
  var k := 0;
  while k < |dict|
    invariant 0 <= k <= |dict|
    invariant found <==> exists i :: 0 <= i < k && dict[i] == word
    decreases |dict| - k
  {
    if dict[k] == word {
      found := true;
      return;
    }
    k := k + 1;
  }
}

method WordBreak(s: seq<int>, dict: seq<seq<int>>) returns (result: bool)
  ensures result == Breakable(s, dict, |s|)
{
  var dp := [true] + seq(|s|, i => false);
  var i := 1;
  while i <= |s|
    invariant 1 <= i <= |s| + 1
    invariant |dp| == |s| + 1
    invariant dp[0] == true
    invariant forall idx :: 0 <= idx < i ==> dp[idx] == Breakable(s, dict, idx)
    invariant forall idx :: i <= idx <= |s| ==> dp[idx] == false
    decreases |s| + 1 - i
  {
    var j := 0;
    var canBreak := false;
    while j < i
      invariant 0 <= j <= i
      invariant canBreak <==> exists k :: 0 <= k < j && Breakable(s, dict, k) && InDict(dict, s[k..i])
      decreases i - j
    {
      if dp[j] {
        assert dp[j] == Breakable(s, dict, j);
        var word := s[j..i];
        var found := FindInDict(dict, word);
        if found {
          canBreak := true;
          break;
        }
      }
      j := j + 1;
    }
    dp := dp[..i] + [canBreak] + dp[i+1..];
    assert dp[i] == canBreak;
    assert canBreak == Breakable(s, dict, i);
    i := i + 1;
  }
  result := dp[|s|];
}
