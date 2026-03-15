// Minimum Jumps
// Task: Add loop invariants so that Dafny can verify this program.
// Given a sequence where a[i] is the max jump length from position i,
// find the minimum number of jumps to reach the last position.

predicate CanReach(a: seq<int>, jumps: seq<int>)
  requires |a| > 0
{
  |jumps| > 0 &&
  jumps[0] == 0 &&
  jumps[|jumps|-1] == |a| - 1 &&
  (forall i :: 0 < i < |jumps| ==> 0 <= jumps[i-1] < jumps[i] < |a|) &&
  (forall i :: 0 < i < |jumps| ==> jumps[i] - jumps[i-1] <= a[jumps[i-1]])
}

predicate IsValidJumpSeq(a: seq<int>, jumps: seq<int>)
  requires |a| > 0
{
  CanReach(a, jumps)
}

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
