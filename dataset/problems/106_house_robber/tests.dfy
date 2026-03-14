// House Robber -- Runtime spec tests

function Max(a: int, b: int): int { if a >= b then a else b }

function Rob(a: seq<int>, n: int): int
  requires 0 <= n <= |a|
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  decreases n
{
  if n == 0 then 0
  else if n == 1 then a[0]
  else Max(Rob(a, n - 1), Rob(a, n - 2) + a[n - 1])
}

method Main()
{
  // Rob: base cases
  expect Rob([5], 0) == 0, "Rob(*, 0) = 0";
  expect Rob([5], 1) == 5, "Rob([5], 1) = 5";

  // Rob: two houses - pick the bigger one
  expect Rob([1, 2], 2) == 2, "Rob([1,2], 2) = 2";
  expect Rob([2, 1], 2) == 2, "Rob([2,1], 2) = 2";

  // Rob: classic example [1, 2, 3, 1]
  // Rob(4) = max(Rob(3), Rob(2) + 1) = max(max(Rob(2), Rob(1)+3), Rob(2) + 1)
  // Rob(1) = 1, Rob(2) = max(1, 2) = 2
  // Rob(3) = max(2, 1+3) = 4, Rob(4) = max(4, 2+1) = 4
  expect Rob([1, 2, 3, 1], 4) == 4, "Rob([1,2,3,1], 4) = 4";

  // Rob: [2, 7, 9, 3, 1]
  // Rob(1)=2, Rob(2)=7, Rob(3)=max(7, 2+9)=11
  // Rob(4)=max(11, 7+3)=11, Rob(5)=max(11, 11+1)=12
  expect Rob([2, 7, 9, 3, 1], 5) == 12, "Rob([2,7,9,3,1], 5) = 12";

  // Rob: negative tests
  expect Rob([1, 2, 3, 1], 4) != 3, "Rob([1,2,3,1]) != 3";
  expect Rob([1, 2, 3, 1], 4) != 6, "Rob([1,2,3,1]) != 6 (sum of all)";

  // Rob: all same
  expect Rob([3, 3, 3, 3], 4) == 6, "Rob([3,3,3,3]) = 6 (pick 1st and 3rd)";

  // Rob: one house
  expect Rob([100], 1) == 100, "Rob([100], 1) = 100";

  print "All spec tests passed\n";
}
