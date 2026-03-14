// Partition Equal Subset Sum -- Runtime spec tests

function SumSeq(a: seq<int>): int
{
  if |a| == 0 then 0 else a[0] + SumSeq(a[1..])
}

function CanPartition(a: seq<int>, n: int, target: int): bool
  requires 0 <= n <= |a|
  decreases n, if target >= 0 then target else 0
{
  if target == 0 then true
  else if target < 0 || n == 0 then false
  else CanPartition(a, n-1, target) || CanPartition(a, n-1, target - a[n-1])
}

method Main()
{
  // SumSeq tests
  expect SumSeq([]) == 0, "SumSeq([]) = 0";
  expect SumSeq([1, 2, 3]) == 6, "SumSeq([1,2,3]) = 6";
  expect SumSeq([5]) == 5, "SumSeq([5]) = 5";
  expect SumSeq([1, 5, 11, 5]) == 22, "SumSeq([1,5,11,5]) = 22";

  // SumSeq: negative test
  expect SumSeq([1, 2, 3, 5]) == 11, "SumSeq([1,2,3,5]) = 11";
  expect SumSeq([1, 2, 3, 5]) != 10, "SumSeq([1,2,3,5]) != 10";

  // CanPartition: base cases
  expect CanPartition([1, 2, 3], 0, 0), "CanPartition(*, 0, 0) is true";
  expect !CanPartition([1, 2, 3], 0, 1), "CanPartition(*, 0, 1) is false";

  // CanPartition: [1, 5, 11, 5] target 11
  // Can select {11}: CanPartition(a, 4, 11) should be true
  expect CanPartition([1, 5, 11, 5], 4, 11), "Can partition [1,5,11,5] to sum 11";

  // CanPartition: [1, 2, 3] target 3
  // Can select {3} or {1,2}
  expect CanPartition([1, 2, 3], 3, 3), "Can partition [1,2,3] to sum 3";

  // CanPartition: not possible
  expect !CanPartition([1, 2, 3], 3, 7), "Cannot partition [1,2,3] to sum 7";

  // Full spec test: partitionable
  var a1 := [1, 5, 11, 5];
  expect SumSeq(a1) % 2 == 0, "Sum of [1,5,11,5] is even";
  expect CanPartition(a1, |a1|, SumSeq(a1) / 2), "[1,5,11,5] can be equal partitioned";

  // Full spec test: odd sum, not partitionable
  var a2 := [1, 2, 3, 5];
  expect SumSeq(a2) % 2 != 0, "Sum of [1,2,3,5] is odd";

  // Full spec test: [0] partitionable (sum=0)
  var a3 := [0];
  expect SumSeq(a3) == 0, "SumSeq([0]) = 0";
  expect SumSeq(a3) % 2 == 0 && CanPartition(a3, |a3|, SumSeq(a3) / 2),
    "[0] can be equal partitioned";

  print "All spec tests passed\n";
}
