// Interval Merging -- Test cases

predicate ValidIntervals(starts: seq<int>, ends: seq<int>)
{ |starts| == |ends| && forall i :: 0 <= i < |starts| ==> starts[i] <= ends[i] }

predicate SortedByStart(starts: seq<int>)
{ forall i, j :: 0 <= i < j < |starts| ==> starts[i] <= starts[j] }

predicate NonOverlapping(starts: seq<int>, ends: seq<int>)
  requires |starts| == |ends|
{ forall i :: 0 <= i < |starts| - 1 ==> ends[i] < starts[i + 1] }

method {:axiom} MergeIntervals(starts: seq<int>, ends: seq<int>) returns (rs: seq<int>, re: seq<int>)
  requires ValidIntervals(starts, ends)
  requires SortedByStart(starts)
  ensures ValidIntervals(rs, re)
  ensures NonOverlapping(rs, re)
  ensures |rs| <= |starts|

method TestOverlapping()
{
  var rs, re := MergeIntervals([1, 2, 5], [3, 4, 7]);
  assert NonOverlapping(rs, re);
}
