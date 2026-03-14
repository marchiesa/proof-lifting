// Merge Overlapping Intervals
// Task: Add loop invariants so that Dafny can verify this program.

predicate SortedByStart(starts: seq<int>)
{
  forall i, j :: 0 <= i < j < |starts| ==> starts[i] <= starts[j]
}

predicate ValidIntervals(starts: seq<int>, ends: seq<int>)
{
  |starts| == |ends| && forall i :: 0 <= i < |starts| ==> starts[i] <= ends[i]
}

predicate NonOverlapping(starts: seq<int>, ends: seq<int>)
  requires |starts| == |ends|
{
  forall i :: 0 <= i < |starts| - 1 ==> ends[i] < starts[i + 1]
}

method MergeIntervals(starts: seq<int>, ends: seq<int>) returns (rs: seq<int>, re: seq<int>)
  requires ValidIntervals(starts, ends)
  requires SortedByStart(starts)
  ensures ValidIntervals(rs, re)
  ensures NonOverlapping(rs, re)
  ensures |rs| <= |starts|
{
  if |starts| == 0 { return [], []; }
  rs := [starts[0]];
  re := [ends[0]];
  var i := 1;
  while i < |starts|
  {
    if starts[i] <= re[|re| - 1] {
      if ends[i] > re[|re| - 1] {
        re := re[..|re| - 1] + [ends[i]];
      }
    } else {
      rs := rs + [starts[i]];
      re := re + [ends[i]];
    }
    i := i + 1;
  }
}
