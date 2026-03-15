// Course Schedule -- Reference solution with invariants

method CanFinish(numCourses: int, prerequisites: seq<(int, int)>) returns (result: bool)
  requires numCourses >= 0
  requires forall i :: 0 <= i < |prerequisites| ==>
    0 <= prerequisites[i].0 < numCourses &&
    0 <= prerequisites[i].1 < numCourses
{
  if numCourses == 0 { result := true; return; }

  var inDeg := new int[numCourses];
  var i := 0;
  while i < numCourses
    invariant 0 <= i <= numCourses
    invariant forall k :: 0 <= k < i ==> inDeg[k] == 0
    decreases numCourses - i
  {
    inDeg[i] := 0;
    i := i + 1;
  }

  i := 0;
  while i < |prerequisites|
    invariant 0 <= i <= |prerequisites|
    invariant forall k :: 0 <= k < numCourses ==> inDeg[k] >= 0
    decreases |prerequisites| - i
  {
    inDeg[prerequisites[i].0] := inDeg[prerequisites[i].0] + 1;
    i := i + 1;
  }

  var queue: seq<int> := [];
  i := 0;
  while i < numCourses
    invariant 0 <= i <= numCourses
    invariant forall k :: 0 <= k < |queue| ==> 0 <= queue[k] < numCourses
    decreases numCourses - i
  {
    if inDeg[i] == 0 {
      queue := queue + [i];
    }
    i := i + 1;
  }

  var count := 0;
  while |queue| > 0
    invariant 0 <= count <= numCourses
    invariant forall k :: 0 <= k < |queue| ==> 0 <= queue[k] < numCourses
    decreases numCourses - count
  {
    var course := queue[0];
    queue := queue[1..];
    count := count + 1;
    if count > numCourses { break; }

    var j := 0;
    while j < |prerequisites|
      invariant 0 <= j <= |prerequisites|
      invariant forall k :: 0 <= k < |queue| ==> 0 <= queue[k] < numCourses
      decreases |prerequisites| - j
    {
      if prerequisites[j].1 == course {
        inDeg[prerequisites[j].0] := inDeg[prerequisites[j].0] - 1;
        if inDeg[prerequisites[j].0] == 0 {
          queue := queue + [prerequisites[j].0];
        }
      }
      j := j + 1;
    }
  }

  result := count == numCourses;
}
