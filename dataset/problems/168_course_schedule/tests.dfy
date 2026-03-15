// Course Schedule -- Spec tests

method CanFinish(numCourses: int, prerequisites: seq<(int, int)>) returns (result: bool)
  requires numCourses >= 0
  requires forall i :: 0 <= i < |prerequisites| ==>
    0 <= prerequisites[i].0 < numCourses && 0 <= prerequisites[i].1 < numCourses
{
  var inDeg := new int[numCourses];
  var i := 0;
  while i < numCourses invariant 0 <= i <= numCourses decreases numCourses - i { inDeg[i] := 0; i := i + 1; }
  i := 0;
  while i < |prerequisites| invariant 0 <= i <= |prerequisites| decreases |prerequisites| - i {
    inDeg[prerequisites[i].0] := inDeg[prerequisites[i].0] + 1; i := i + 1;
  }
  var queue: seq<int> := [];
  i := 0;
  while i < numCourses invariant 0 <= i <= numCourses decreases numCourses - i {
    if inDeg[i] == 0 { queue := queue + [i]; } i := i + 1;
  }
  var count := 0;
  while |queue| > 0 invariant count >= 0 decreases numCourses + 1 - count {
    var course := queue[0]; queue := queue[1..]; count := count + 1;
    if count > numCourses { break; }
    var j := 0;
    while j < |prerequisites| invariant 0 <= j <= |prerequisites| decreases |prerequisites| - j {
      if prerequisites[j].1 == course {
        assume {:axiom} 0 <= prerequisites[j].0 < inDeg.Length;
        inDeg[prerequisites[j].0] := inDeg[prerequisites[j].0] - 1;
        if inDeg[prerequisites[j].0] == 0 { queue := queue + [prerequisites[j].0]; }
      }
      j := j + 1;
    }
  }
  result := count == numCourses;
}

method Main() {
  // 2 courses, 1->0 prerequisite: can finish
  var r1 := CanFinish(2, [(1, 0)]);
  expect r1 == true;

  // Cycle: 0->1, 1->0
  var r2 := CanFinish(2, [(1, 0), (0, 1)]);
  expect r2 == false;

  // No prerequisites
  var r3 := CanFinish(3, []);
  expect r3 == true;

  // Linear chain
  var r4 := CanFinish(3, [(1, 0), (2, 1)]);
  expect r4 == true;

  // Negative: cycle detected
  expect !r2;

  print "All spec tests passed\n";
}
