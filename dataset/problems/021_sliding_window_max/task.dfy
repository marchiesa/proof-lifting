// Sliding Window Maximum
// Task: Add loop invariants so that Dafny can verify this program.
// Note: The SeqMaxIsMax lemma also needs a proof body (not loop invariants,
// but a structural induction proof). The main verification task is the method.

function SeqMax(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then s[0]
  else
    var rest := SeqMax(s[1..]);
    if s[0] > rest then s[0] else rest
}

lemma SeqMaxIsMax(s: seq<int>)
  requires |s| > 0
  ensures forall i :: 0 <= i < |s| ==> s[i] <= SeqMax(s)
  ensures exists i :: 0 <= i < |s| && s[i] == SeqMax(s)
{
  if |s| > 1 {
    SeqMaxIsMax(s[1..]);
  }
}

lemma SeqMaxFromScan(s: seq<int>, maxVal: int)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] <= maxVal
  requires exists i :: 0 <= i < |s| && s[i] == maxVal
  ensures SeqMax(s) == maxVal
{
  SeqMaxIsMax(s);
  var k :| 0 <= k < |s| && s[k] == maxVal;
  assert s[k] <= SeqMax(s);
  assert SeqMax(s) <= maxVal;
}

method SlidingMax(a: seq<int>, w: int) returns (result: seq<int>)
  requires |a| > 0
  requires 1 <= w <= |a|
  ensures |result| == |a| - w + 1
  ensures forall i :: 0 <= i < |result| ==> result[i] == SeqMax(a[i..i + w])
{
  result := [];
  var i := 0;
  while i <= |a| - w
  {
    // Find max in window a[i..i+w]
    var maxVal := a[i];
    var maxIdx := i;
    var j := i + 1;
    while j < i + w
    {
      if a[j] > maxVal {
        maxVal := a[j];
        maxIdx := j;
      }
      j := j + 1;
    }
    assert forall k {:trigger a[i..i + w][k]} :: 0 <= k < w ==> a[i..i + w][k] == a[i + k];
    assert forall k {:trigger a[i + k]} :: 0 <= k < w ==> a[i + k] <= maxVal;
    assert a[maxIdx] == maxVal;
    assert i <= maxIdx < i + w;
    assert a[i..i + w][maxIdx - i] == maxVal;
    SeqMaxFromScan(a[i..i + w], maxVal);
    result := result + [maxVal];
    i := i + 1;
  }
}
