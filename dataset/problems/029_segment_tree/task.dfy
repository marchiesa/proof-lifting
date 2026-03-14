// Prefix Minimum Query (Simulated Segment Tree)
// Task: Add loop invariants so that Dafny can verify this program.

function SeqMin(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then s[0]
  else
    var rest := SeqMin(s[1..]);
    if s[0] < rest then s[0] else rest
}

lemma SeqMinProperty(s: seq<int>)
  requires |s| > 0
  ensures forall i :: 0 <= i < |s| ==> SeqMin(s) <= s[i]
  ensures SeqMin(s) in multiset(s)
{
  if |s| > 1 {
    SeqMinProperty(s[1..]);
  }
}

lemma SeqMinExtend(s: seq<int>, x: int)
  requires |s| > 0
  ensures SeqMin(s + [x]) == if SeqMin(s) <= x then SeqMin(s) else x
{
  if |s| == 1 {
    assert s + [x] == [s[0], x];
    assert (s + [x])[1..] == [x];
  } else {
    assert (s + [x])[0] == s[0];
    assert (s + [x])[1..] == s[1..] + [x];
    SeqMinExtend(s[1..], x);
  }
}

method BuildPrefixMin(a: seq<int>) returns (prefixMin: seq<int>)
  requires |a| > 0
  ensures |prefixMin| == |a|
  ensures prefixMin[0] == a[0]
  ensures forall i :: 0 <= i < |a| ==> prefixMin[i] == SeqMin(a[..i + 1])
{
  prefixMin := [a[0]];
  var i := 1;
  while i < |a|
  {
    var newMin := if prefixMin[i - 1] <= a[i] then prefixMin[i - 1] else a[i];
    prefixMin := prefixMin + [newMin];
    i := i + 1;
  }
}
