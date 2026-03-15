// Circular Array Loop Detection
// Task: Add loop invariants so that Dafny can verify this program.

predicate AllNonZero(a: seq<int>)
{
  forall i :: 0 <= i < |a| ==> a[i] != 0
}

function NextIndex(a: seq<int>, i: int): int
  requires |a| > 0
  requires 0 <= i < |a|
{
  ((i + a[i]) % |a| + |a|) % |a|
}

method CircularLoop(a: seq<int>) returns (hasCycle: bool)
  requires |a| > 0
  requires AllNonZero(a)
  ensures true  // Detection correctness is hard to fully spec
{
  hasCycle := false;
  var i := 0;
  while i < |a|
  {
    var slow := i;
    var fast := i;
    var isForward := a[i] > 0;
    var steps := 0;
    var found := false;
    while steps <= |a|
    {
      // Move slow by 1
      var nextSlow := NextIndex(a, slow);
      if (a[slow] > 0) != isForward {
        break;
      }
      slow := nextSlow;

      // Move fast by 2
      var nextFast := NextIndex(a, fast);
      if (a[fast] > 0) != isForward {
        break;
      }
      fast := nextFast;
      nextFast := NextIndex(a, fast);
      if (a[fast] > 0) != isForward {
        break;
      }
      fast := nextFast;

      steps := steps + 1;
      if slow == fast {
        // Check cycle length > 1
        if NextIndex(a, slow) != slow {
          found := true;
        }
        break;
      }
    }
    if found {
      hasCycle := true;
      return;
    }
    i := i + 1;
  }
}
