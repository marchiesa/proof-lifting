// Maximum Sum Rectangle -- Test cases

function RowSum(row: seq<int>, c1: int, c2: int): int
  requires 0 <= c1 <= c2 <= |row|
  decreases c2 - c1
{
  if c1 == c2 then 0 else row[c1] + RowSum(row, c1 + 1, c2)
}

method Main()
{
  expect RowSum([1, 2, 3], 0, 3) == 6, "RowSum [1,2,3] = 6";
  expect RowSum([1, -2, 3], 0, 3) == 2, "RowSum [1,-2,3] = 2";
  expect RowSum([1, -2, 3], 2, 3) == 3, "RowSum [3] = 3";
  expect RowSum([], 0, 0) == 0, "RowSum empty = 0";

  // Negative: wrong values
  expect RowSum([1, 2, 3], 0, 3) != 5, "RowSum [1,2,3] != 5";

  print "All spec tests passed\n";
}
