// Problem 6: Interval Scheduling Maximization with Optimality (Greedy)
//
// Given intervals [start, end), find the maximum-cardinality set of
// non-overlapping intervals using the greedy earliest-end-time algorithm.
//
// The spec requires OPTIMALITY via exchange argument: no selection has more intervals.

// An interval
datatype Interval = Interval(start: nat, end: nat)

// Two intervals are non-overlapping (don't conflict)
ghost predicate NonOverlapping(a: Interval, b: Interval)
{
  a.end <= b.start || b.end <= a.start
}

// A set of intervals (by index) are pairwise non-overlapping
ghost predicate PairwiseNonOverlapping(intervals: seq<Interval>, selection: set<nat>)
  requires forall i :: i in selection ==> i < |intervals|
{
  forall i, j :: i in selection && j in selection && i != j ==>
    NonOverlapping(intervals[i], intervals[j])
}

// A selection is valid: indices in range and pairwise non-overlapping
ghost predicate ValidSelection(intervals: seq<Interval>, selection: set<nat>)
{
  (forall i :: i in selection ==> i < |intervals|) &&
  PairwiseNonOverlapping(intervals, selection)
}

// Well-formed intervals: start < end for all
ghost predicate WellFormedIntervals(intervals: seq<Interval>)
{
  forall i :: 0 <= i < |intervals| ==> intervals[i].start < intervals[i].end
}

// Sorted by end time
ghost predicate SortedByEnd(intervals: seq<Interval>)
{
  forall i, j :: 0 <= i < j < |intervals| ==> intervals[i].end <= intervals[j].end
}

// OPTIMALITY spec: the returned count is the maximum over all valid selections
ghost predicate IsMaxSelection(intervals: seq<Interval>, selected: set<nat>, count: nat)
{
  ValidSelection(intervals, selected) &&
  |selected| == count &&
  // No valid selection has more intervals
  (forall other: set<nat> :: ValidSelection(intervals, other) ==> |other| <= count)
}

// Helper: insertion sort by end time (returns sorted permutation as indices)
method SortByEndTime(intervals: seq<Interval>) returns (sorted: seq<nat>)
  requires |intervals| > 0
  ensures |sorted| == |intervals|
  // sorted is a permutation of 0..|intervals|-1
  ensures forall i :: 0 <= i < |intervals| ==> i in sorted
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] != sorted[j]
  // sorted order by end time
  ensures forall i, j :: 0 <= i < j < |sorted| ==>
    intervals[sorted[i]].end <= intervals[sorted[j]].end
{
  // Build index array
  var arr := new nat[|intervals|];
  var i := 0;
  while i < |intervals|
  {
    arr[i] := i;
    i := i + 1;
  }

  // Insertion sort by end time
  i := 1;
  while i < |intervals|
  {
    var key := arr[i];
    var j := i - 1;
    while j >= 0 && intervals[arr[j]].end > intervals[key].end
    {
      arr[j + 1] := arr[j];
      j := j - 1;
    }
    arr[j + 1] := key;
    i := i + 1;
  }

  sorted := arr[..];
}

// Main method: Greedy interval scheduling
// Returns the maximum number of non-overlapping intervals
method MaxNonOverlapping(intervals: seq<Interval>) returns (count: nat, selected: set<nat>)
  requires |intervals| > 0
  requires WellFormedIntervals(intervals)
  ensures IsMaxSelection(intervals, selected, count)
{
  // Sort intervals by end time
  var sortedIdx := SortByEndTime(intervals);

  // Greedy: pick earliest ending non-overlapping interval
  selected := {};
  var lastEnd := 0;
  var first := true;

  var i := 0;
  while i < |sortedIdx|
  {
    var idx := sortedIdx[i];
    if first || intervals[idx].start >= lastEnd {
      selected := selected + {idx};
      lastEnd := intervals[idx].end;
      first := false;
    }
    i := i + 1;
  }

  count := |selected|;
}
