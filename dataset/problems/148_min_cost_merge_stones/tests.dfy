// Minimum Cost to Merge Stones -- Test cases

function SumRange(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else a[lo] + SumRange(a, lo + 1, hi)
}

method Main()
{
  expect SumRange([3, 2, 4], 0, 3) == 9, "Sum [3,2,4] = 9";
  expect SumRange([3, 2, 4], 0, 2) == 5, "Sum [3,2] = 5";
  expect SumRange([1], 0, 1) == 1, "Sum [1] = 1";

  // Single stone: cost 0
  // Two stones [3, 5]: cost 8
  // Three stones [3, 2, 4]: merge (3,2)=5 cost 5, merge (5,4)=9 cost 9, total 14
  //   or merge (2,4)=6 cost 6, merge (3,6)=9 cost 9, total 15
  //   min = 14

  expect SumRange([3, 2, 4], 0, 3) != 10, "Sum != 10";

  print "All spec tests passed\n";
}
