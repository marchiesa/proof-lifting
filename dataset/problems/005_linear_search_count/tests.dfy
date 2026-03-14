// Count Occurrences -- Runtime spec tests

function CountSpec(a: seq<int>, target: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[0] == target then 1 else 0) + CountSpec(a[1..], target)
}

method Main()
{
  // Test CountSpec
  expect CountSpec([1, 3, 5, 3, 3, 7], 3) == 3, "should count 3 occurrences of 3";
  expect CountSpec([1, 2, 3], 4) == 0, "should count 0 occurrences of 4";
  expect CountSpec([], 1) == 0, "empty sequence has 0 occurrences";
  expect CountSpec([7, 7, 7], 7) == 3, "all-match should count 3";
  expect CountSpec([42], 42) == 1, "single match should count 1";
  expect CountSpec([42], 0) == 0, "single non-match should count 0";

  // Negative cases
  expect CountSpec([1, 2, 3, 4, 5], 6) == 0, "no 6 in [1..5]";
  expect CountSpec([1, 1, 1, 1], 1) == 4, "four 1s should count 4";
  expect CountSpec([1, 2, 1, 2, 1], 1) == 3, "alternating: 3 ones";
  expect CountSpec([1, 2, 1, 2, 1], 2) == 2, "alternating: 2 twos";

  print "All spec tests passed\n";
}
