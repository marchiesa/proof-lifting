// Run-Length Encoding -- Runtime spec tests

function Repeat(v: int, n: int): seq<int>
  requires n > 0
  decreases n
{
  if n == 1 then [v]
  else [v] + Repeat(v, n - 1)
}

function Expand(values: seq<int>, counts: seq<int>): seq<int>
  requires |values| == |counts|
  requires forall i | 0 <= i < |counts| :: counts[i] > 0
  decreases |values|
{
  if |values| == 0 then []
  else Repeat(values[0], counts[0]) + Expand(values[1..], counts[1..])
}

method Main()
{
  // Test Repeat
  expect Repeat(5, 1) == [5], "repeat 5 once";
  expect Repeat(5, 3) == [5, 5, 5], "repeat 5 three times";
  expect Repeat(0, 2) == [0, 0], "repeat 0 twice";
  expect |Repeat(1, 4)| == 4, "repeat length check";

  // Test Expand
  expect Expand([], []) == [], "expand empty";
  expect Expand([5], [1]) == [5], "expand single value, count 1";
  expect Expand([5], [3]) == [5, 5, 5], "expand single value, count 3";
  expect Expand([1, 2], [2, 3]) == [1, 1, 2, 2, 2], "expand [1x2, 2x3]";
  expect Expand([1, 2, 3], [1, 1, 1]) == [1, 2, 3], "expand all count 1";

  // Test round-trip: Expand of a known RLE should give original
  // [1, 1, 2, 2, 2, 3] -> values=[1,2,3], counts=[2,3,1]
  expect Expand([1, 2, 3], [2, 3, 1]) == [1, 1, 2, 2, 2, 3],
    "RLE roundtrip: expand([1,2,3],[2,3,1]) == [1,1,2,2,2,3]";

  // [5, 5, 5, 5] -> values=[5], counts=[4]
  expect Expand([5], [4]) == [5, 5, 5, 5],
    "RLE roundtrip: expand([5],[4]) == [5,5,5,5]";

  // Alternating [1, 2, 1] -> values=[1,2,1], counts=[1,1,1]
  expect Expand([1, 2, 1], [1, 1, 1]) == [1, 2, 1],
    "alternating RLE roundtrip";

  print "All spec tests passed\n";
}
