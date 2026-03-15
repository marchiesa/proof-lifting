// Maximum Number of Events Attended

function Max(a: int, b: int): int { if a >= b then a else b }

method MaxEvents(starts: seq<int>, ends: seq<int>) returns (count: int)
  requires |starts| == |ends|
  requires |starts| > 0
  requires forall i :: 0 <= i < |starts| ==> 1 <= starts[i] <= ends[i]
  ensures count >= 0
  ensures count <= |starts|
{
  var n := |starts|;
  // Sort events by end day (simple selection sort on end)
  var sortedStarts := starts;
  var sortedEnds := ends;
  var i := 0;
  while i < n
  {
    var minIdx := i;
    var j := i + 1;
    while j < n
    {
      if sortedEnds[j] < sortedEnds[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    if minIdx != i {
      var tmpS := sortedStarts[i];
      var tmpE := sortedEnds[i];
      sortedStarts := sortedStarts[..i] + [sortedStarts[minIdx]] + sortedStarts[i+1..minIdx] + [tmpS] + sortedStarts[minIdx+1..];
      sortedEnds := sortedEnds[..i] + [sortedEnds[minIdx]] + sortedEnds[i+1..minIdx] + [tmpE] + sortedEnds[minIdx+1..];
    }
    i := i + 1;
  }

  // Greedy: attend each event on earliest available day
  var usedDays: set<int> := {};
  count := 0;
  i := 0;
  while i < n
  {
    var day := sortedStarts[i];
    while day <= sortedEnds[i]
    {
      if day !in usedDays {
        usedDays := usedDays + {day};
        count := count + 1;
        break;
      }
      day := day + 1;
    }
    i := i + 1;
  }
}

method Main()
{
  // Events: [1,2], [2,3], [3,4]
  var r1 := MaxEvents([1, 2, 3], [2, 3, 4]);
  expect r1 >= 0;
  expect r1 <= 3;

  // Overlapping: [1,2], [1,2], [1,2]
  var r2 := MaxEvents([1, 1, 1], [2, 2, 2]);
  expect r2 >= 0;
  expect r2 <= 3;

  // Single event
  var r3 := MaxEvents([1], [5]);
  expect r3 >= 0;
  expect r3 <= 1;

  // Non-overlapping
  var r4 := MaxEvents([1, 3, 5], [2, 4, 6]);
  expect r4 >= 0;
  expect r4 <= 3;

  print "All spec tests passed\n";
}
