// Find Minimum in Rotated Sorted Array
// Task: Add loop invariants so that Dafny can verify this program.

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

lemma SeqMinSplit(a: seq<int>, k: int)
  requires |a| > 0
  requires 0 < k < |a|
  ensures SeqMin(a) == if SeqMin(a[..k]) <= SeqMin(a[k..]) then SeqMin(a[..k]) else SeqMin(a[k..])
  decreases |a|
{
  SeqMinIsMin(a);
  SeqMinIsMin(a[..k]);
  SeqMinIsMin(a[k..]);
  forall i | 0 <= i < |a|
    ensures SeqMin(a) <= a[i]
  {}
  var idx :| 0 <= idx < |a| && a[idx] == SeqMin(a);
  if idx < k {
    assert a[idx] == a[..k][idx];
  } else {
    assert a[idx] == a[k..][idx - k];
  }
}

method FindMin(a: seq<int>) returns (min: int)
  requires |a| > 0
  ensures min == SeqMin(a)
{
  SeqMinIsMin(a);
  min := a[0];
  var i := 1;
  while i < |a|
  {
    if a[i] < min {
      min := a[i];
    }
    i := i + 1;
  }
}
