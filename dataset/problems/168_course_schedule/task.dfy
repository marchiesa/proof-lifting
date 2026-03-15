// Course Schedule (detect if all courses completable -- topological sort)
// Task: Add loop invariants so that Dafny can verify this program.

// Graph: numCourses, prerequisites[i] = (course, prerequisite)
// Return true if all courses can be finished (no cycle)
method CanFinish(numCourses: int, prerequisites: seq<(int, int)>) returns (result: bool)
  requires numCourses >= 0
  requires forall i :: 0 <= i < |prerequisites| ==>
    0 <= prerequisites[i].0 < numCourses &&
    0 <= prerequisites[i].1 < numCourses
  ensures result ==> true  // can finish all courses
{
  // Compute in-degree
  var inDeg := new int[numCourses];
  var i := 0;
  while i < numCourses
  {
    inDeg[i] := 0;
    i := i + 1;
  }

  i := 0;
  while i < |prerequisites|
  {
    inDeg[prerequisites[i].0] := inDeg[prerequisites[i].0] + 1;
    i := i + 1;
  }

  // Initialize queue with courses having in-degree 0
  var queue: seq<int> := [];
  i := 0;
  while i < numCourses
  {
    if inDeg[i] == 0 {
      queue := queue + [i];
    }
    i := i + 1;
  }

  var count := 0;
  while |queue| > 0
  {
    var course := queue[0];
    queue := queue[1..];
    count := count + 1;

    // Reduce in-degree of neighbors
    var j := 0;
    while j < |prerequisites|
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
