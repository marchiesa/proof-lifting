// Interval Scheduling (Greedy)
// Task: Add loop invariants so that Dafny can verify this program.

predicate SortedByEnd(ends: seq<int>)
{
  forall i, j :: 0 <= i < j < |ends| ==> ends[i] <= ends[j]
}

// Greedy interval scheduling: pick non-overlapping intervals sorted by end time
method IntervalSchedule(starts: seq<int>, ends: seq<int>) returns (count: int, selected: seq<int>)
  requires |starts| == |ends|
  requires SortedByEnd(ends)
  requires forall i :: 0 <= i < |starts| ==> starts[i] < ends[i]
  ensures 0 <= count <= |starts|
  ensures |selected| == count
  ensures forall i :: 0 <= i < count ==> 0 <= selected[i] < |starts|
  // Selected indices are in increasing order
  ensures forall i, j :: 0 <= i < j < count ==> selected[i] < selected[j]
  // Selected intervals are non-overlapping
  ensures forall i, j :: 0 <= i < j < count ==>
    ends[selected[i]] <= starts[selected[j]]
{
  count := 0;
  selected := [];
  var lastEnd := -1;
  var i := 0;

  while i < |starts|
  {
    if starts[i] >= lastEnd {
      selected := selected + [i];
      count := count + 1;
      lastEnd := ends[i];
    }
    i := i + 1;
  }
}
