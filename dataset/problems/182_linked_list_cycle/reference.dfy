// Linked List Cycle Detection -- Reference solution with invariants

predicate ValidList(next: seq<int>)
{
  forall i :: 0 <= i < |next| ==> (next[i] == -1 || (0 <= next[i] < |next|))
}

method DetectCycle(next: seq<int>, start: int) returns (hasCycle: bool)
  requires ValidList(next)
  requires -1 <= start < |next|
  requires |next| > 0
  ensures hasCycle ==> start != -1
{
  if start == -1 {
    return false;
  }
  var slow := start;
  var fast := start;
  var steps := 0;
  while steps < |next|
    invariant 0 <= steps <= |next|
    invariant 0 <= slow < |next|
    invariant 0 <= fast < |next|
    invariant start != -1
    decreases |next| - steps
  {
    // Advance fast two steps
    var f1 := next[fast];
    if f1 == -1 {
      return false;
    }
    var f2 := next[f1];
    if f2 == -1 {
      return false;
    }
    // Advance slow one step
    var s1 := next[slow];
    if s1 == -1 {
      return false;
    }
    slow := s1;
    fast := f2;
    steps := steps + 1;
    if slow == fast {
      return true;
    }
  }
  return true;
}
