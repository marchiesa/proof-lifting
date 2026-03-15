// Circular Array Loop Detection -- Reference solution with invariants

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

lemma NextIndexBounds(a: seq<int>, i: int)
  requires |a| > 0
  requires 0 <= i < |a|
  ensures 0 <= NextIndex(a, i) < |a|
{
  var n := |a|;
  var raw := (i + a[i]) % n;
  var adjusted := (raw + n) % n;
  assert 0 <= adjusted < n;
}

method CircularLoop(a: seq<int>) returns (hasCycle: bool)
  requires |a| > 0
  requires AllNonZero(a)
  ensures true
{
  hasCycle := false;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    decreases |a| - i
  {
    var slow := i;
    var fast := i;
    var isForward := a[i] > 0;
    var steps := 0;
    var found := false;
    var broken := false;
    while steps <= |a| && !found && !broken
      invariant 0 <= slow < |a|
      invariant 0 <= fast < |a|
      invariant 0 <= steps <= |a| + 1
      decreases |a| + 1 - steps
    {
      NextIndexBounds(a, slow);
      var nextSlow := NextIndex(a, slow);
      if (a[slow] > 0) != isForward {
        broken := true;
      } else {
        slow := nextSlow;

        NextIndexBounds(a, fast);
        var nextFast := NextIndex(a, fast);
        if (a[fast] > 0) != isForward {
          broken := true;
        } else {
          fast := nextFast;
          NextIndexBounds(a, fast);
          nextFast := NextIndex(a, fast);
          if (a[fast] > 0) != isForward {
            broken := true;
          } else {
            fast := nextFast;
            steps := steps + 1;
            if slow == fast {
              NextIndexBounds(a, slow);
              if NextIndex(a, slow) != slow {
                found := true;
              } else {
                broken := true;
              }
            }
          }
        }
      }
    }
    if found {
      hasCycle := true;
      return;
    }
    i := i + 1;
  }
}
