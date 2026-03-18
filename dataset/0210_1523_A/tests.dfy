// --- Formal specification ---

function CountAliveNeighbors(cells: seq<int>, i: int): int
  requires 0 <= i < |cells|
{
  (if i > 0 && cells[i - 1] == 1 then 1 else 0) +
  (if i < |cells| - 1 && cells[i + 1] == 1 then 1 else 0)
}

function CellNextState(cells: seq<int>, i: int): int
  requires 0 <= i < |cells|
{
  if cells[i] == 1 then 1
  else if CountAliveNeighbors(cells, i) == 1 then 1
  else 0
}

function BuildEvolved(cells: seq<int>, k: int): seq<int>
  requires 0 <= k <= |cells|
  ensures |BuildEvolved(cells, k)| == k
  decreases k
{
  if k == 0 then []
  else BuildEvolved(cells, k - 1) + [CellNextState(cells, k - 1)]
}

function EvolveOnce(cells: seq<int>): seq<int>
  ensures |EvolveOnce(cells)| == |cells|
{
  BuildEvolved(cells, |cells|)
}

function Evolve(cells: seq<int>, m: int): seq<int>
  requires m >= 0
  decreases m
{
  if m == 0 then cells
  else
    var next := EvolveOnce(cells);
    if next == cells then cells
    else Evolve(next, m - 1)
}

predicate ValidCells(cells: seq<int>)
{
  forall i | 0 <= i < |cells| :: cells[i] == 0 || cells[i] == 1
}

// --- Implementation ---

method GameOfLife(cells: seq<int>, m: int) returns (result: seq<int>)
  requires ValidCells(cells)
  requires m >= 0
  ensures result == Evolve(cells, m)
{
  var n := |cells|;
  if n == 0 {
    result := [];
    return;
  }
  var INF := 10000000000;

  var left: seq<int> := [];
  var last1 := -INF;
  var i := 0;
  while i < n
  {
    if cells[i] == 1 {
      last1 := i;
    }
    left := left + [last1];
    i := i + 1;
  }

  var right: seq<int> := [];
  i := 0;
  while i < n
  {
    right := right + [INF];
    i := i + 1;
  }
  last1 := INF;
  i := n - 1;
  while i >= 0
  {
    if cells[i] == 1 {
      last1 := i;
    }
    right := right[i := last1];
    i := i - 1;
  }

  var ans: seq<int> := [];
  i := 0;
  while i < n
  {
    if left[i] == i {
      ans := ans + [1];
    } else if (i - left[i] <= m || right[i] - i <= m) && i - left[i] != right[i] - i {
      ans := ans + [1];
    } else {
      ans := ans + [0];
    }
    i := i + 1;
  }
  result := ans;
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // ensures: result == Evolve(cells, m)
  // Using small inputs (length 1-3) to keep spec evaluation fast

  expect Evolve([0,0,0], 100) == [0,0,0], "spec positive 1";       // from Test 1.4
  expect Evolve([1,0,1], 1000000000) == [1,0,1], "spec positive 2"; // from Test 5 (fixed point)
  expect Evolve([1,1,1], 1) == [1,1,1], "spec positive 3";          // from Test 8.1
  expect Evolve([0,0], 2) == [0,0], "spec positive 4";              // from Test 8.2
  expect Evolve([0,1,0], 1) == [1,1,1], "spec positive 5";          // derived: non-trivial evolution
  expect Evolve([1,0,0], 1) == [1,1,0], "spec positive 6";          // derived: single step
  expect Evolve([1,0,0], 2) == [1,1,1], "spec positive 7";          // derived: two steps

  // ===== SPEC NEGATIVE TESTS =====
  // Wrong outputs must be rejected by the spec

  expect Evolve([1,0,1], 1000000000) != [1,0,2], "spec negative 1"; // from Neg 5
  expect Evolve([1,1,1], 1) != [1,1,2], "spec negative 2";          // from Neg 8
  expect Evolve([0,1,0], 1) != [1,1,2], "spec negative 3";          // scaled from Neg 1
  expect Evolve([1,0], 1) != [1,2], "spec negative 4";              // scaled from Neg 3
  expect Evolve([0,0,0], 1) != [0,0,1], "spec negative 5";          // scaled from Neg 9
  expect Evolve([0,0], 2) != [0,1], "spec negative 6";              // from Neg 8 (second case)
  expect Evolve([1,0,0], 1) != [1,1,1], "spec negative 7";          // scaled from Neg 2

  // ===== IMPLEMENTATION TESTS =====

  var r1 := GameOfLife([0,1,0,0,0,0,0,0,0,0,1], 3);
  expect r1 == [1,1,1,1,1,0,0,1,1,1,1], "impl test 1.1 failed";

  var r2 := GameOfLife([0,1,1,0,1,0,0,1,0,1], 2);
  expect r2 == [1,1,1,0,1,1,1,1,0,1], "impl test 1.2 failed";

  var r3 := GameOfLife([1,0,1,0,1], 2);
  expect r3 == [1,0,1,0,1], "impl test 1.3 failed";

  var r4 := GameOfLife([0,0,0], 100);
  expect r4 == [0,0,0], "impl test 1.4 failed";

  var r5 := GameOfLife([1,0,0,0,0,1,0,0,0,0,1], 1);
  expect r5 == [1,1,0,0,1,1,1,0,0,1,1], "impl test 2 failed";

  var r6 := GameOfLife([1,0,1,0], 1000000000);
  expect r6 == [1,0,1,1], "impl test 3 failed";

  var r7 := GameOfLife([1,1,0,1,1], 42069);
  expect r7 == [1,1,0,1,1], "impl test 4 failed";

  var r8 := GameOfLife([1,0,1], 1000000000);
  expect r8 == [1,0,1], "impl test 5 failed";

  var r9 := GameOfLife([1,1,0,1,1], 1000000000);
  expect r9 == [1,1,0,1,1], "impl test 6 failed";

  var r10 := GameOfLife([1,1,1,1,1,1,1,1,1,0,1], 1000000000);
  expect r10 == [1,1,1,1,1,1,1,1,1,0,1], "impl test 7 failed";

  var r11 := GameOfLife([1,1,1], 1);
  expect r11 == [1,1,1], "impl test 8.1 failed";

  var r12 := GameOfLife([0,0], 2);
  expect r12 == [0,0], "impl test 8.2 failed";

  var r13 := GameOfLife([1,1,1,1,1,1,1,1,1,1], 1);
  expect r13 == [1,1,1,1,1,1,1,1,1,1], "impl test 9.1 failed";

  var r14 := GameOfLife([0,0,0,0,0,0,0,0,0], 4);
  expect r14 == [0,0,0,0,0,0,0,0,0], "impl test 9.2 failed";

  var r15 := GameOfLife([0,0,0,0,0,0,0,0,0], 4);
  expect r15 == [0,0,0,0,0,0,0,0,0], "impl test 9.3 failed";

  var r16 := GameOfLife([0,0,0,0,0,0,0,0,0], 4);
  expect r16 == [0,0,0,0,0,0,0,0,0], "impl test 9.4 failed";

  print "All tests passed\n";
}