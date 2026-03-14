// Pascal's Triangle Row -- Runtime spec tests

function Choose(n: nat, k: nat): nat
  decreases n, k
{
  if k == 0 then 1
  else if n == 0 then 0
  else Choose(n-1, k-1) + Choose(n-1, k)
}

function PascalRow(n: nat): seq<nat>
{
  seq(n + 1, k requires 0 <= k <= n => Choose(n, k))
}

method Main()
{
  // Choose: base cases
  expect Choose(0, 0) == 1, "C(0,0) = 1";
  expect Choose(5, 0) == 1, "C(5,0) = 1";
  expect Choose(0, 1) == 0, "C(0,1) = 0";

  // Choose: known values
  expect Choose(4, 2) == 6, "C(4,2) = 6";
  expect Choose(5, 2) == 10, "C(5,2) = 10";
  expect Choose(5, 3) == 10, "C(5,3) = 10";
  expect Choose(3, 1) == 3, "C(3,1) = 3";
  expect Choose(4, 4) == 1, "C(4,4) = 1";

  // Choose: negative tests
  expect Choose(4, 2) != 4, "C(4,2) != 4";
  expect Choose(3, 2) != 2, "C(3,2) != 2";

  // PascalRow: row 0
  expect PascalRow(0) == [1], "Row 0 = [1]";

  // PascalRow: row 1
  expect PascalRow(1) == [1, 1], "Row 1 = [1,1]";

  // PascalRow: row 2
  expect PascalRow(2) == [1, 2, 1], "Row 2 = [1,2,1]";

  // PascalRow: row 3
  expect PascalRow(3) == [1, 3, 3, 1], "Row 3 = [1,3,3,1]";

  // PascalRow: row 4
  expect PascalRow(4) == [1, 4, 6, 4, 1], "Row 4 = [1,4,6,4,1]";

  // PascalRow: negative test
  expect PascalRow(3) != [1, 3, 1, 3], "Row 3 != [1,3,1,3]";

  // PascalRow: length check
  expect |PascalRow(5)| == 6, "Row 5 has 6 elements";

  print "All spec tests passed\n";
}
