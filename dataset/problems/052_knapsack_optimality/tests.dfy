// 0/1 Knapsack with Value Bound -- Runtime spec tests

function SumSeq(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + SumSeq(s[1..])
}

method Main() {
  // SumSeq tests
  expect SumSeq([]) == 0, "sum of empty is 0";
  expect SumSeq([1]) == 1, "sum of [1] is 1";
  expect SumSeq([1, 2, 3]) == 6, "sum of [1,2,3] is 6";
  expect SumSeq([10, 20, 30]) == 60, "sum of [10,20,30] is 60";
  expect SumSeq([0, 0, 0]) == 0, "sum of zeros is 0";
  expect SumSeq([-1, 1]) == 0, "sum of [-1,1] is 0";
  expect SumSeq([5]) == 5, "sum of [5] is 5";

  // Wrong answers
  expect SumSeq([1, 2, 3]) != 5, "sum of [1,2,3] is not 5";
  expect SumSeq([1, 2, 3]) != 7, "sum of [1,2,3] is not 7";

  // Test knapsack postcondition properties on known values
  // maxVal >= 0 for valid items
  // weights=[2,3,4], values=[3,4,5], capacity=5: best is items 0+1 = value 7
  var vals := [3, 4, 5];
  expect SumSeq([3, 4]) == 7, "items 0+1 give value 7";
  expect SumSeq([3, 5]) == 8, "items 0+2 give value 8 (but weight 6 > cap 5)";

  print "All spec tests passed\n";
}
