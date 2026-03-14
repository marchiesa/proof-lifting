// Sliding Window Maximum -- Runtime spec tests

function SeqMax(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then s[0]
  else
    var rest := SeqMax(s[1..]);
    if s[0] > rest then s[0] else rest
}

method Main()
{
  // Test SeqMax
  expect SeqMax([1]) == 1, "max of [1] is 1";
  expect SeqMax([1, 2, 3]) == 3, "max of [1,2,3] is 3";
  expect SeqMax([3, 2, 1]) == 3, "max of [3,2,1] is 3";
  expect SeqMax([1, 5, 2]) == 5, "max of [1,5,2] is 5";
  expect SeqMax([-3, -1, -5]) == -1, "max of negatives is -1";
  expect SeqMax([42]) == 42, "max of single element";
  expect SeqMax([7, 7, 7]) == 7, "max of all same is that value";

  // Test SeqMax on windows (simulating sliding window)
  var a := [1, 3, -1, -3, 5, 3, 6, 7];
  // Window size 3: windows are [1,3,-1], [3,-1,-3], [-1,-3,5], [-3,5,3], [5,3,6], [3,6,7]
  expect SeqMax(a[0..3]) == 3, "window [1,3,-1] max is 3";
  expect SeqMax(a[1..4]) == 3, "window [3,-1,-3] max is 3";
  expect SeqMax(a[2..5]) == 5, "window [-1,-3,5] max is 5";
  expect SeqMax(a[3..6]) == 5, "window [-3,5,3] max is 5";
  expect SeqMax(a[4..7]) == 6, "window [5,3,6] max is 6";
  expect SeqMax(a[5..8]) == 7, "window [3,6,7] max is 7";

  // Window size 1
  expect SeqMax(a[0..1]) == 1, "window size 1 at index 0";
  expect SeqMax(a[7..8]) == 7, "window size 1 at last index";

  // Full window
  expect SeqMax(a[0..8]) == 7, "full window max is 7";

  print "All spec tests passed\n";
}
