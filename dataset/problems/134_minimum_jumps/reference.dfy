// Minimum Jumps -- Reference solution with invariants

method MinJumps(a: seq<int>) returns (result: int)
  requires |a| > 0
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures result >= 0
  ensures result == 0 <==> |a| == 1
{
  if |a| == 1 {
    return 0;
  }
  result := 0;
  var curEnd := 0;
  var farthest := 0;
  var i := 0;
  while i < |a| - 1
    invariant 0 <= i <= |a| - 1
    invariant result >= 0
    invariant farthest >= 0
    invariant 0 <= curEnd
    invariant i > 0 ==> result >= 1
    invariant i == 0 ==> curEnd == 0
    decreases |a| - 1 - i
  {
    if i + a[i] > farthest {
      farthest := i + a[i];
    }
    if i == curEnd {
      result := result + 1;
      curEnd := farthest;
    }
    i := i + 1;
  }
}
