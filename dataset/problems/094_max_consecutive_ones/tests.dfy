// Maximum Consecutive Ones -- Runtime spec tests

function RunOfOnes(a: seq<int>, i: int): int
  requires 0 <= i <= |a|
  decreases i
{
  if i == 0 then 0
  else if a[i-1] == 1 then 1 + RunOfOnes(a, i-1)
  else 0
}

function MaxRun(a: seq<int>, i: int): int
  requires 0 <= i <= |a|
  decreases i
{
  if i == 0 then 0
  else
    var cur := RunOfOnes(a, i);
    var prev := MaxRun(a, i-1);
    if cur > prev then cur else prev
}

method Main()
{
  // RunOfOnes tests
  expect RunOfOnes([1, 1, 0, 1, 1, 1], 0) == 0, "RunOfOnes at 0 is 0";
  expect RunOfOnes([1, 1, 0, 1, 1, 1], 1) == 1, "RunOfOnes at 1";
  expect RunOfOnes([1, 1, 0, 1, 1, 1], 2) == 2, "RunOfOnes at 2";
  expect RunOfOnes([1, 1, 0, 1, 1, 1], 3) == 0, "RunOfOnes at 3 (after 0)";
  expect RunOfOnes([1, 1, 0, 1, 1, 1], 6) == 3, "RunOfOnes at 6";

  // MaxRun tests: positive
  expect MaxRun([1, 1, 0, 1, 1, 1], 6) == 3, "MaxRun of [1,1,0,1,1,1] is 3";
  expect MaxRun([1, 1, 1], 3) == 3, "MaxRun of all ones is 3";
  expect MaxRun([0, 0, 0], 3) == 0, "MaxRun of all zeros is 0";
  expect MaxRun([], 0) == 0, "MaxRun of empty is 0";
  expect MaxRun([1], 1) == 1, "MaxRun of [1] is 1";
  expect MaxRun([0], 1) == 0, "MaxRun of [0] is 0";

  // MaxRun: negative
  expect MaxRun([1, 1, 0, 1, 1, 1], 6) != 2, "MaxRun should not be 2";
  expect MaxRun([1, 0, 1], 3) != 2, "MaxRun of [1,0,1] should not be 2";

  // Edge cases
  expect MaxRun([1, 0, 1], 3) == 1, "MaxRun of [1,0,1] is 1";
  expect MaxRun([0, 1, 0], 3) == 1, "MaxRun of [0,1,0] is 1";

  print "All spec tests passed\n";
}
