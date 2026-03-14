// Word Break -- Test cases

predicate InDict(dict: seq<seq<int>>, word: seq<int>)
{ exists i :: 0 <= i < |dict| && dict[i] == word }

function Breakable(s: seq<int>, dict: seq<seq<int>>, n: int): bool
  requires 0 <= n <= |s|
  decreases n
{
  if n == 0 then true
  else exists k :: 0 <= k < n && Breakable(s, dict, k) && InDict(dict, s[k..n])
}

method {:axiom} WordBreak(s: seq<int>, dict: seq<seq<int>>) returns (result: bool)
  ensures result == Breakable(s, dict, |s|)

method TestBasic()
{
  var s := [1, 2, 1, 2];
  var dict := [[1, 2]];
  var r := WordBreak(s, dict);
}

method TestEmpty()
{
  var s: seq<int> := [];
  var dict := [[1]];
  var r := WordBreak(s, dict);
  assert r;
}
