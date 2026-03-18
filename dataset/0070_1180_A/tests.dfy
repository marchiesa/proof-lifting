function Abs(x: int): int
{
  if x >= 0 then x else -x
}

predicate InRhombus(x: int, y: int, n: int)
  requires n >= 1
{
  Abs(x) + Abs(y) <= n - 1
}

function RowWidth(x: int, r: int): int
  requires r >= 0
{
  if Abs(x) > r then 0
  else 2 * (r - Abs(x)) + 1
}

function SumRows(lo: int, hi: int, r: int): int
  requires r >= 0
  decreases if lo <= hi then hi - lo + 1 else 0
{
  if lo > hi then 0
  else RowWidth(lo, r) + SumRows(lo + 1, hi, r)
}

function RhombusCellCount(n: int): int
  requires n >= 1
{
  SumRows(-(n - 1), n - 1, n - 1)
}

method Rhombus(n: int) returns (cells: int)
  requires n >= 1
  ensures cells == RhombusCellCount(n)
{
  cells := 1;
  var i := 1;
  while i < n
  {
    cells := cells + i * 4;
    i := i + 1;
  }
}

method Main()
{
  // ========== SPEC POSITIVE TESTS ==========
  // Test: RhombusCellCount(n) == expected
  expect RhombusCellCount(1) == 1, "spec positive 1";
  expect RhombusCellCount(2) == 5, "spec positive 2";
  expect RhombusCellCount(3) == 13, "spec positive 3";
  expect RhombusCellCount(11) == 221, "spec positive 4";
  expect RhombusCellCount(21) == 841, "spec positive 5";
  expect RhombusCellCount(31) == 1861, "spec positive 6";
  expect RhombusCellCount(41) == 3281, "spec positive 7";
  expect RhombusCellCount(51) == 5101, "spec positive 8";
  expect RhombusCellCount(100) == 19801, "spec positive 9";
  expect RhombusCellCount(34) == 2245, "spec positive 10";

  // ========== SPEC NEGATIVE TESTS ==========
  // Test: RhombusCellCount(n) != wrong_output
  expect RhombusCellCount(1) != 2, "spec negative 1";
  expect RhombusCellCount(2) != 6, "spec negative 2";
  expect RhombusCellCount(3) != 14, "spec negative 3";
  expect RhombusCellCount(11) != 222, "spec negative 4";
  expect RhombusCellCount(21) != 842, "spec negative 5";
  expect RhombusCellCount(31) != 1862, "spec negative 6";
  expect RhombusCellCount(41) != 3282, "spec negative 7";
  expect RhombusCellCount(51) != 5102, "spec negative 8";
  expect RhombusCellCount(100) != 19802, "spec negative 9";
  expect RhombusCellCount(34) != 2246, "spec negative 10";

  // ========== IMPLEMENTATION TESTS ==========
  var result: int;

  result := Rhombus(1);
  expect result == 1, "impl test 1 failed";

  result := Rhombus(2);
  expect result == 5, "impl test 2 failed";

  result := Rhombus(3);
  expect result == 13, "impl test 3 failed";

  result := Rhombus(11);
  expect result == 221, "impl test 4 failed";

  result := Rhombus(21);
  expect result == 841, "impl test 5 failed";

  result := Rhombus(31);
  expect result == 1861, "impl test 6 failed";

  result := Rhombus(41);
  expect result == 3281, "impl test 7 failed";

  result := Rhombus(51);
  expect result == 5101, "impl test 8 failed";

  result := Rhombus(100);
  expect result == 19801, "impl test 9 failed";

  result := Rhombus(34);
  expect result == 2245, "impl test 10 failed";

  print "All tests passed\n";
}