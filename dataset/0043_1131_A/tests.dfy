// ---- Testable spec (predicates and functions) ----

predicate IsShipCell(x: int, y: int, w1: int, h1: int, w2: int, h2: int)
{
  (1 <= x <= w1 && 1 <= y <= h1) ||
  (1 <= x <= w2 && h1 + 1 <= y <= h1 + h2)
}

predicate IsMarkedCell(x: int, y: int, w1: int, h1: int, w2: int, h2: int)
{
  !IsShipCell(x, y, w1, h1, w2, h2) &&
  exists dx | -1 <= dx <= 1 ::
    exists dy | -1 <= dy <= 1 ::
      !(dx == 0 && dy == 0) && IsShipCell(x + dx, y + dy, w1, h1, w2, h2)
}

function CountMarkedRow(x: int, xHi: int, y: int,
                        w1: int, h1: int, w2: int, h2: int): int
  decreases xHi - x + 1
{
  if x > xHi then 0
  else (if IsMarkedCell(x, y, w1, h1, w2, h2) then 1 else 0)
       + CountMarkedRow(x + 1, xHi, y, w1, h1, w2, h2)
}

function CountMarkedGrid(y: int, yHi: int, xLo: int, xHi: int,
                         w1: int, h1: int, w2: int, h2: int): int
  decreases yHi - y + 1
{
  if y > yHi then 0
  else CountMarkedRow(xLo, xHi, y, w1, h1, w2, h2)
       + CountMarkedGrid(y + 1, yHi, xLo, xHi, w1, h1, w2, h2)
}

function TotalMarked(w1: int, h1: int, w2: int, h2: int): int
  requires w1 >= 1 && h1 >= 1 && w2 >= 1 && h2 >= 1 && w1 >= w2
{
  CountMarkedGrid(0, h1 + h2 + 1, 0, w1 + 1, w1, h1, w2, h2)
}

// ---- Implementation ----

method SeaBattle(w1: int, h1: int, w2: int, h2: int) returns (marked: int)
  requires w1 >= 1 && h1 >= 1 && w2 >= 1 && h2 >= 1 && w1 >= w2
  ensures marked == TotalMarked(w1, h1, w2, h2)
{
  marked := (w1 + 2) * (h1 + h2 + 2) - (w1 - w2) * h2 - w1 * h1 - w2 * h2;
}

// ---- Tests ----

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Testing TotalMarked (the top-level ensures predicate) with small inputs.
  // Tests 1-3 use original pairs directly (already small).
  // Tests 4-10 use small equivalent cases (large originals would be too slow).
  expect TotalMarked(2, 1, 2, 1) == 12, "spec positive 1";
  expect TotalMarked(2, 2, 1, 2) == 16, "spec positive 2";
  expect TotalMarked(1, 1, 1, 1) == 10, "spec positive 3";
  expect TotalMarked(1, 2, 1, 1) == 12, "spec positive 4";
  expect TotalMarked(2, 1, 1, 1) == 12, "spec positive 5";
  expect TotalMarked(3, 1, 1, 1) == 14, "spec positive 6";
  expect TotalMarked(1, 1, 1, 2) == 12, "spec positive 7";
  expect TotalMarked(3, 2, 2, 1) == 16, "spec positive 8";
  expect TotalMarked(3, 3, 2, 2) == 20, "spec positive 9";
  expect TotalMarked(2, 2, 2, 2) == 16, "spec positive 10";

  // ===== SPEC NEGATIVE TESTS =====
  // Testing that TotalMarked rejects wrong outputs (each off by +1).
  expect TotalMarked(2, 1, 2, 1) != 13, "spec negative 1";
  expect TotalMarked(2, 2, 1, 2) != 17, "spec negative 2";
  expect TotalMarked(1, 1, 1, 1) != 11, "spec negative 3";
  expect TotalMarked(1, 2, 1, 1) != 13, "spec negative 4";
  expect TotalMarked(2, 1, 1, 1) != 13, "spec negative 5";
  expect TotalMarked(3, 1, 1, 1) != 15, "spec negative 6";
  expect TotalMarked(1, 1, 1, 2) != 13, "spec negative 7";
  expect TotalMarked(3, 2, 2, 1) != 17, "spec negative 8";
  expect TotalMarked(3, 3, 2, 2) != 21, "spec negative 9";
  expect TotalMarked(2, 2, 2, 2) != 17, "spec negative 10";

  // ===== IMPLEMENTATION TESTS (full-size inputs) =====
  var r: int;

  r := SeaBattle(2, 1, 2, 1);
  expect r == 12, "impl test 1 failed";

  r := SeaBattle(2, 2, 1, 2);
  expect r == 16, "impl test 2 failed";

  r := SeaBattle(1, 1, 1, 1);
  expect r == 10, "impl test 3 failed";

  r := SeaBattle(1, 50, 1, 50);
  expect r == 206, "impl test 4 failed";

  r := SeaBattle(6, 4, 2, 7);
  expect r == 38, "impl test 5 failed";

  r := SeaBattle(100000000, 100000000, 99999999, 100000000);
  expect r == 600000004, "impl test 6 failed";

  r := SeaBattle(100000000, 1, 100000000, 1);
  expect r == 200000008, "impl test 7 failed";

  r := SeaBattle(19661988, 30021918, 8795449, 27534575);
  expect r == 154436966, "impl test 8 failed";

  r := SeaBattle(98948781, 84140283, 95485812, 84557929);
  expect r == 535293990, "impl test 9 failed";

  r := SeaBattle(47, 40, 42, 49);
  expect r == 276, "impl test 10 failed";

  print "All tests passed\n";
}