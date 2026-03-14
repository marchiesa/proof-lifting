// Count Elements Greater Than Threshold -- Runtime spec tests

function CountGreater(s: seq<int>, threshold: int): nat
{
  if |s| == 0 then 0
  else (if s[0] > threshold then 1 else 0) + CountGreater(s[1..], threshold)
}

method Main() {
  // Basic cases
  expect CountGreater([1, 5, 3, 7, 2], 3) == 2, "two elements > 3";
  expect CountGreater([10, 20, 30], 0) == 3, "all elements > 0";
  expect CountGreater([1, 2, 3], 10) == 0, "no elements > 10";
  expect CountGreater([], 5) == 0, "empty seq has count 0";

  // Edge cases
  expect CountGreater([5], 5) == 0, "equal to threshold not counted";
  expect CountGreater([5], 4) == 1, "one above threshold";
  expect CountGreater([1, 1, 1, 1], 0) == 4, "all above zero";
  expect CountGreater([0, 0, 0], 0) == 0, "none above zero when equal";

  // Wrong answer check
  expect CountGreater([1, 5, 3, 7, 2], 3) != 3, "should not be 3";
  expect CountGreater([1, 5, 3, 7, 2], 3) != 1, "should not be 1";

  print "All spec tests passed\n";
}
