// Interval Scheduling (Greedy) -- Reference solution with invariants

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
    invariant 0 <= i <= |starts|
    invariant 0 <= count <= i
    invariant |selected| == count
    invariant forall k :: 0 <= k < count ==> 0 <= selected[k] < i
    invariant forall k, l :: 0 <= k < l < count ==> selected[k] < selected[l]
    invariant forall k, l :: 0 <= k < l < count ==>
      ends[selected[k]] <= starts[selected[l]]
    invariant count > 0 ==> lastEnd == ends[selected[count - 1]]
    invariant count > 0 ==> forall k :: 0 <= k < count ==> ends[selected[k]] <= lastEnd
    invariant count == 0 ==> lastEnd == -1
    decreases |starts| - i
  {
    if starts[i] >= lastEnd {
      // All previously selected intervals end at or before lastEnd
      // which is <= starts[i], so new interval doesn't overlap
      selected := selected + [i];
      count := count + 1;
      lastEnd := ends[i];
    }
    i := i + 1;
  }
}
