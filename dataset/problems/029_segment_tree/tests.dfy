// Prefix Minimum Query -- Runtime spec tests

function SeqMin(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then s[0]
  else
    var rest := SeqMin(s[1..]);
    if s[0] < rest then s[0] else rest
}

method Main()
{
  // Test SeqMin
  expect SeqMin([5]) == 5, "min of [5] is 5";
  expect SeqMin([5, 4, 3, 2, 1]) == 1, "min of descending is 1";
  expect SeqMin([1, 2, 3, 4, 5]) == 1, "min of ascending is 1";
  expect SeqMin([3, 1, 4, 1, 5]) == 1, "min of [3,1,4,1,5] is 1";
  expect SeqMin([-5, -3, -1]) == -5, "min of negatives is -5";
  expect SeqMin([7, 7, 7]) == 7, "min of all same is 7";
  expect SeqMin([42]) == 42, "min of single element";

  // Test prefix minimum property:
  // For a = [3, 1, 4, 1, 5]:
  //   prefixMin[0] = SeqMin([3]) = 3
  //   prefixMin[1] = SeqMin([3,1]) = 1
  //   prefixMin[2] = SeqMin([3,1,4]) = 1
  //   prefixMin[3] = SeqMin([3,1,4,1]) = 1
  //   prefixMin[4] = SeqMin([3,1,4,1,5]) = 1
  var a := [3, 1, 4, 1, 5];
  expect SeqMin(a[..1]) == 3, "prefix min at index 0";
  expect SeqMin(a[..2]) == 1, "prefix min at index 1";
  expect SeqMin(a[..3]) == 1, "prefix min at index 2";
  expect SeqMin(a[..4]) == 1, "prefix min at index 3";
  expect SeqMin(a[..5]) == 1, "prefix min at index 4";

  // For a = [5, 4, 3, 2, 1] (decreasing):
  //   prefixMin = [5, 4, 3, 2, 1]
  var b := [5, 4, 3, 2, 1];
  expect SeqMin(b[..1]) == 5, "decreasing prefix min at 0";
  expect SeqMin(b[..2]) == 4, "decreasing prefix min at 1";
  expect SeqMin(b[..3]) == 3, "decreasing prefix min at 2";
  expect SeqMin(b[..4]) == 2, "decreasing prefix min at 3";
  expect SeqMin(b[..5]) == 1, "decreasing prefix min at 4";

  // For a = [1, 2, 3, 4, 5] (increasing):
  //   prefixMin = [1, 1, 1, 1, 1]
  var c := [1, 2, 3, 4, 5];
  expect SeqMin(c[..1]) == 1, "increasing prefix min at 0";
  expect SeqMin(c[..2]) == 1, "increasing prefix min at 1";
  expect SeqMin(c[..5]) == 1, "increasing prefix min at 4";

  print "All spec tests passed\n";
}
