// Find Minimum in Rotated Sorted Array -- Reference solution with invariants

function SeqMin(a: seq<int>): int
  requires |a| > 0
  decreases |a|
{
  if |a| == 1 then a[0]
  else if a[0] <= SeqMin(a[1..]) then a[0]
  else SeqMin(a[1..])
}

lemma SeqMinIsMin(a: seq<int>)
  requires |a| > 0
  ensures forall i :: 0 <= i < |a| ==> SeqMin(a) <= a[i]
  ensures exists i :: 0 <= i < |a| && a[i] == SeqMin(a)
  decreases |a|
{
  if |a| == 1 {
    assert a[0] == SeqMin(a);
  } else {
    SeqMinIsMin(a[1..]);
    forall i | 0 <= i < |a|
      ensures SeqMin(a) <= a[i]
    { if i > 0 { assert a[i] == a[1..][i-1]; } }
    if a[0] <= SeqMin(a[1..]) {
      assert a[0] == SeqMin(a);
    } else {
      var j :| 0 <= j < |a[1..]| && a[1..][j] == SeqMin(a[1..]);
      assert a[j+1] == a[1..][j];
      assert a[j+1] == SeqMin(a);
    }
  }
}

lemma SeqMinPrefix(a: seq<int>, k: int)
  requires |a| > 0
  requires 1 <= k < |a|
  ensures SeqMin(a[..k+1]) == if a[k] <= SeqMin(a[..k]) then a[k] else SeqMin(a[..k])
  decreases |a|
{
  SeqMinIsMin(a[..k]);
  SeqMinIsMin(a[..k+1]);
  var s1 := a[..k];
  var s2 := a[..k+1];
  assert s2 == s1 + [a[k]];
  forall i | 0 <= i < |s2|
    ensures SeqMin(s2) <= s2[i]
  {}
}

method FindMin(a: seq<int>) returns (min: int)
  requires |a| > 0
  ensures min == SeqMin(a)
{
  SeqMinIsMin(a);
  min := a[0];
  var i := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant min == SeqMin(a[..i])
    decreases |a| - i
  {
    SeqMinPrefix(a, i);
    assert a[..i+1] == a[..i] + [a[i]];
    if a[i] < min {
      min := a[i];
    }
    i := i + 1;
  }
  assert a[..i] == a;
}
