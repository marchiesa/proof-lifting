// Jump Game -- Runtime spec tests

function MaxReach(a: seq<int>, n: int): int
  requires forall k :: 0 <= k < |a| ==> a[k] >= 0
  requires 0 <= n <= |a|
{
  if n == 0 then 0
  else
    var prev := MaxReach(a, n - 1);
    if n - 1 <= prev then
      if n - 1 + a[n-1] > prev then n - 1 + a[n-1] else prev
    else prev
}

method Main()
{
  // MaxReach: reachable case [2, 3, 1, 1, 4]
  expect MaxReach([2, 3, 1, 1, 4], 0) == 0, "MaxReach at 0 is 0";
  expect MaxReach([2, 3, 1, 1, 4], 1) == 2, "MaxReach at 1 is 0+2=2";
  expect MaxReach([2, 3, 1, 1, 4], 2) == 4, "MaxReach at 2 is 1+3=4";
  expect MaxReach([2, 3, 1, 1, 4], 5) >= 4, "MaxReach at 5 >= 4 (last index)";

  // Reachable: MaxReach >= |a| - 1
  var a1 := [2, 3, 1, 1, 4];
  expect MaxReach(a1, |a1|) >= |a1| - 1, "[2,3,1,1,4] is reachable";

  // Unreachable case [3, 2, 1, 0, 4]
  var a2 := [3, 2, 1, 0, 4];
  expect MaxReach(a2, |a2|) < |a2| - 1, "[3,2,1,0,4] is not reachable";

  // Single element: always reachable
  expect MaxReach([0], 1) >= 0, "Single element is reachable";

  // Two elements, can jump
  expect MaxReach([1, 0], 2) >= 1, "[1,0] is reachable";

  // Two elements, can't jump
  expect MaxReach([0, 1], 2) < 1, "[0,1] is not reachable (stuck at 0)";

  // All zeros except first
  expect MaxReach([5, 0, 0, 0, 0], 5) >= 4, "[5,0,0,0,0] is reachable";

  // Negative test
  expect MaxReach([1, 0, 1], 3) < 2, "[1,0,1] cannot reach index 2";

  print "All spec tests passed\n";
}
