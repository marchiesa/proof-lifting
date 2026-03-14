// Interval Merging -- Runtime spec tests

// Bounded compilable versions of spec predicates

method SortedByStartCheck(starts: seq<int>) returns (result: bool)
{
  if |starts| <= 1 { return true; }
  var i := 0;
  while i < |starts| - 1
  {
    if starts[i] > starts[i + 1] { return false; }
    i := i + 1;
  }
  return true;
}

method ValidIntervalsCheck(starts: seq<int>, ends: seq<int>) returns (result: bool)
{
  if |starts| != |ends| { return false; }
  var i := 0;
  while i < |starts|
  {
    if starts[i] > ends[i] { return false; }
    i := i + 1;
  }
  return true;
}

method NonOverlappingCheck(starts: seq<int>, ends: seq<int>) returns (result: bool)
  requires |starts| == |ends|
{
  if |starts| <= 1 { return true; }
  var i := 0;
  while i < |starts| - 1
  {
    if ends[i] >= starts[i + 1] { return false; }
    i := i + 1;
  }
  return true;
}

method Main()
{
  // Test SortedByStart
  var r := SortedByStartCheck([1, 2, 5]);
  expect r, "[1,2,5] should be sorted by start";

  r := SortedByStartCheck([5, 2, 1]);
  expect !r, "[5,2,1] should not be sorted by start";

  r := SortedByStartCheck([1, 1, 2]);
  expect r, "[1,1,2] should be sorted (equal allowed)";

  r := SortedByStartCheck([]);
  expect r, "[] should be sorted";

  // Test ValidIntervals
  r := ValidIntervalsCheck([1, 2, 5], [3, 4, 7]);
  expect r, "Intervals (1,3),(2,4),(5,7) should be valid";

  r := ValidIntervalsCheck([1, 5], [3, 4]);
  expect !r, "Interval (5,4) is invalid (start > end)";

  r := ValidIntervalsCheck([1], [1]);
  expect r, "Point interval (1,1) is valid";

  // Test NonOverlapping
  r := NonOverlappingCheck([1, 5], [3, 7]);
  expect r, "[1,3] and [5,7] are non-overlapping";

  r := NonOverlappingCheck([1, 3], [4, 7]);
  expect !r, "[1,4] and [3,7] overlap (end 4 >= start 3)";

  r := NonOverlappingCheck([1, 5, 10], [3, 7, 12]);
  expect r, "Three non-overlapping intervals";

  r := NonOverlappingCheck([1], [5]);
  expect r, "Single interval is non-overlapping";

  r := NonOverlappingCheck([], []);
  expect r, "Empty is non-overlapping";

  // Test combined: merging [1,3],[2,4],[5,7] should give [1,4],[5,7]
  var rs := [1, 5];
  var re := [4, 7];
  r := ValidIntervalsCheck(rs, re);
  expect r, "Merged result should be valid intervals";
  r := NonOverlappingCheck(rs, re);
  expect r, "Merged result should be non-overlapping";
  expect |rs| <= 3, "Merged result should have <= original count";

  // Negative: overlapping merged result would be invalid
  r := NonOverlappingCheck([1, 3], [5, 7]);
  expect !r, "Intervals [1,5] and [3,7] overlap";

  print "All spec tests passed\n";
}
