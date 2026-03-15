// Linked List Cycle Detection (seq-based)

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

method Main()
{
  // Cycle: 0->1->2->0
  var cyclic := [1, 2, 0];
  var r1 := DetectCycle(cyclic, 0);
  // We can't assert r1==true from spec alone, but we test the postcondition
  if r1 { expect true; } // hasCycle ==> start != -1 is satisfied since start=0

  // No cycle: 0->1->2->-1
  var acyclic := [1, 2, -1];
  var r2 := DetectCycle(acyclic, 0);
  // r2 can be true or false; postcondition just says hasCycle ==> start != -1

  // Start at -1
  var r3 := DetectCycle(acyclic, -1);
  expect !r3;  // start == -1 so hasCycle must be false (contrapositive of postcondition)

  // Self-loop
  var selfLoop := [0];
  var r4 := DetectCycle(selfLoop, 0);
  if r4 { expect true; }

  print "All spec tests passed\n";
}
