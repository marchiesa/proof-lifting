// Linked List Cycle Detection (seq-based)
// Task: Add loop invariants so that Dafny can verify this program.

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
  {
    if fast == -1 || next[fast] == -1 {
      return false;
    }
    slow := next[slow];
    fast := next[next[fast]];
    steps := steps + 1;
    if slow == fast {
      return true;
    }
  }
  // If we exhaust |next| steps without termination, there must be a cycle
  return true;
}
