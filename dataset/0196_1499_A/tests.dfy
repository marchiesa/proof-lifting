datatype Domino = Domino(row: int, col: int, horizontal: bool)

function Cell1Row(d: Domino): int { d.row }
function Cell1Col(d: Domino): int { d.col }
function Cell2Row(d: Domino): int { if d.horizontal then d.row else 1 - d.row }
function Cell2Col(d: Domino): int { if d.horizontal then d.col + 1 else d.col }

predicate ValidDomino(d: Domino, n: int)
{
  n >= 0 &&
  if d.horizontal then
    (d.row == 0 || d.row == 1) && 0 <= d.col && d.col + 1 < n
  else
    d.row == 0 && 0 <= d.col && d.col < n
}

predicate CellIsWhite(row: int, col: int, k1: int, k2: int)
{
  (row == 0 && col < k1) || (row == 1 && col < k2)
}

predicate IsWhiteDomino(d: Domino, k1: int, k2: int)
{
  CellIsWhite(Cell1Row(d), Cell1Col(d), k1, k2) &&
  CellIsWhite(Cell2Row(d), Cell2Col(d), k1, k2)
}

predicate IsBlackDomino(d: Domino, n: int, k1: int, k2: int)
{
  !CellIsWhite(Cell1Row(d), Cell1Col(d), k1, k2) &&
  !CellIsWhite(Cell2Row(d), Cell2Col(d), k1, k2)
}

predicate DominoesOverlap(d1: Domino, d2: Domino)
{
  var r1a := Cell1Row(d1); var c1a := Cell1Col(d1);
  var r1b := Cell2Row(d1); var c1b := Cell2Col(d1);
  var r2a := Cell1Row(d2); var c2a := Cell1Col(d2);
  var r2b := Cell2Row(d2); var c2b := Cell2Col(d2);
  (r1a == r2a && c1a == c2a) || (r1a == r2b && c1a == c2b) ||
  (r1b == r2a && c1b == c2a) || (r1b == r2b && c1b == c2b)
}

predicate NoOverlaps(placement: seq<Domino>)
{
  forall i, j | 0 <= i < |placement| && 0 <= j < |placement| && i != j ::
    !DominoesOverlap(placement[i], placement[j])
}

function CountWhite(placement: seq<Domino>, k1: int, k2: int): int
  decreases |placement|
{
  if |placement| == 0 then 0
  else
    (if IsWhiteDomino(placement[|placement|-1], k1, k2) then 1 else 0) +
    CountWhite(placement[..|placement|-1], k1, k2)
}

function CountBlack(placement: seq<Domino>, n: int, k1: int, k2: int): int
  decreases |placement|
{
  if |placement| == 0 then 0
  else
    (if IsBlackDomino(placement[|placement|-1], n, k1, k2) then 1 else 0) +
    CountBlack(placement[..|placement|-1], n, k1, k2)
}

predicate AllDominoesValid(placement: seq<Domino>, n: int, k1: int, k2: int)
{
  forall i | 0 <= i < |placement| ::
    ValidDomino(placement[i], n) &&
    (IsWhiteDomino(placement[i], k1, k2) || IsBlackDomino(placement[i], n, k1, k2))
}

predicate ValidPlacement(placement: seq<Domino>, n: int, k1: int, k2: int, w: int, b: int)
{
  |placement| == w + b &&
  AllDominoesValid(placement, n, k1, k2) &&
  NoOverlaps(placement) &&
  CountWhite(placement, k1, k2) == w &&
  CountBlack(placement, n, k1, k2) == b
}

function DecodeDomino(e: int): Domino
{
  Domino((e / 2) % 2, e / 4, (e % 2) == 1)
}

function BuildPlacement(encoding: seq<int>): seq<Domino>
  decreases |encoding|
{
  if |encoding| == 0 then []
  else BuildPlacement(encoding[..|encoding|-1]) + [DecodeDomino(encoding[|encoding|-1])]
}

predicate ValidEncodedPlacement(encoding: seq<int>, n: int, k1: int, k2: int, w: int, b: int)
{
  |encoding| == w + b &&
  (forall i | 0 <= i < |encoding| :: 0 <= encoding[i] < 4 * n) &&
  ValidPlacement(BuildPlacement(encoding), n, k1, k2, w, b)
}

predicate CanPlace(n: int, k1: int, k2: int, w: int, b: int)
  requires n >= 1
  requires 0 <= k1 <= n && 0 <= k2 <= n
  requires w >= 0 && b >= 0
{
  ExistsPlacement([], w + b, 4 * n, n, k1, k2, w, b)
}

predicate ExistsPlacement(partial: seq<int>, remaining: int, domainSize: int,
                          n: int, k1: int, k2: int, w: int, b: int)
  requires domainSize >= 0
  requires remaining >= 0
  decreases remaining
{
  if remaining == 0 then
    ValidEncodedPlacement(partial, n, k1, k2, w, b)
  else
    exists e | 0 <= e < domainSize ::
      ExistsPlacement(partial + [e], remaining - 1, domainSize, n, k1, k2, w, b)
}

method DominoOnWindowsill(n: int, k1: int, k2: int, w: int, b: int) returns (result: bool)
  requires n >= 1
  requires 0 <= k1 <= n && 0 <= k2 <= n
  requires w >= 0 && b >= 0
  ensures result == CanPlace(n, k1, k2, w, b)
{
  var r1 := n - k1;
  var r2 := n - k2;

  var diffK := k1 - k2;
  if diffK < 0 { diffK := -diffK; }

  var diffR := r1 - r2;
  if diffR < 0 { diffR := -diffR; }

  var minK := if k1 < k2 then k1 else k2;
  var minR := if r1 < r2 then r1 else r2;

  var W := minK + diffK / 2;
  var B := minR + diffR / 2;

  result := W >= w && B >= b;
}

method Main()
{
  var r: bool;

  // ===== SPEC POSITIVE TESTS =====
  // CanPlace uses bounded existential enumeration; keep inputs small.

  // From Test 5: n=1,k1=0,k2=0,w=0,b=0 -> true (search space: 1)
  expect CanPlace(1, 0, 0, 0, 0) == true, "spec positive 1";

  // From Test 1.1/2.x: n=1,k1=0,k2=1,w=1,b=0 -> false (search space: 4)
  expect CanPlace(1, 0, 1, 1, 0) == false, "spec positive 2";

  // From Test 1.2: n=1,k1=1,k2=1,w=0,b=0 -> true (search space: 1)
  expect CanPlace(1, 1, 1, 0, 0) == true, "spec positive 3";

  // From Test 12: n=2,k1=1,k2=0,w=0,b=1 -> true (search space: 8)
  expect CanPlace(2, 1, 0, 0, 1) == true, "spec positive 4";

  // From Test 8.3: n=3,k1=1,k2=1,w=0,b=2 -> true (search space: 144)
  expect CanPlace(3, 1, 1, 0, 2) == true, "spec positive 5";

  // From Test 6: n=3,k1=3,k2=3,w=3,b=0 -> true (search space: 1728)
  expect CanPlace(3, 3, 3, 3, 0) == true, "spec positive 6";

  // Scaled from Test 10 (n=7,k1=7,k2=0,w=3,b=3 -> n=2,k1=2,k2=0,w=1,b=1): true (search space: 64)
  expect CanPlace(2, 2, 0, 1, 1) == true, "spec positive 7";

  // Scaled from Test 7 (n=6,k1=0,k2=0,w=0,b=6 -> n=1,k1=0,k2=0,w=0,b=1): true (search space: 4)
  expect CanPlace(1, 0, 0, 0, 1) == true, "spec positive 8";

  // ===== SPEC NEGATIVE TESTS =====
  // Verify CanPlace rejects the wrong output value.
  // Neg 1,2,8 are format-only diffs (trailing " WRONG" text), not boolean flips; skipped.

  // From Neg 5: n=1,k1=0,k2=0,w=0,b=0 correct=true, wrong=false
  expect CanPlace(1, 0, 0, 0, 0) != false, "spec negative 1";

  // Scaled from Neg 4 (n=10,k1=10,k2=10,w=5,b=5 correct=false, wrong=true
  //   -> n=1,k1=0,k2=0,w=1,b=0 correct=false, wrong=true) (search space: 4)
  expect CanPlace(1, 0, 0, 1, 0) != true, "spec negative 2";

  // Scaled from Neg 3 (n=5,k1=3,k2=4,w=2,b=1 correct=true, wrong=false
  //   -> n=2,k1=2,k2=2,w=1,b=0 correct=true, wrong=false) (search space: 8)
  expect CanPlace(2, 2, 2, 1, 0) != false, "spec negative 3";

  // From Neg 6: n=3,k1=3,k2=3,w=3,b=0 correct=true, wrong=false (search space: 1728)
  expect CanPlace(3, 3, 3, 3, 0) != false, "spec negative 4";

  // Scaled from Neg 7 (n=6,k1=0,k2=0,w=0,b=6 correct=true, wrong=false
  //   -> n=1,k1=0,k2=0,w=0,b=1 correct=true, wrong=false) (search space: 4)
  expect CanPlace(1, 0, 0, 0, 1) != false, "spec negative 5";

  // Scaled from Neg 9 (n=50,k1=25,k2=30,w=10,b=8 correct=true, wrong=false
  //   -> n=2,k1=1,k2=2,w=1,b=0 correct=true, wrong=false) (search space: 8)
  expect CanPlace(2, 1, 2, 1, 0) != false, "spec negative 6";

  // Scaled from Neg 10 (n=7,k1=7,k2=0,w=3,b=3 correct=true, wrong=false
  //   -> n=2,k1=2,k2=0,w=1,b=1 correct=true, wrong=false) (search space: 64)
  expect CanPlace(2, 2, 0, 1, 1) != false, "spec negative 7";

  // ===== IMPLEMENTATION TESTS =====
  // Full-size inputs — the method is O(1).

  // Test 1 (5 cases)
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "impl test 1.1";
  r := DominoOnWindowsill(1, 1, 1, 0, 0);
  expect r == true, "impl test 1.2";
  r := DominoOnWindowsill(3, 0, 0, 1, 3);
  expect r == false, "impl test 1.3";
  r := DominoOnWindowsill(4, 3, 1, 2, 2);
  expect r == true, "impl test 1.4";
  r := DominoOnWindowsill(5, 4, 3, 3, 1);
  expect r == true, "impl test 1.5";

  // Test 2 (9 identical cases)
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "impl test 2.1";
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "impl test 2.2";
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "impl test 2.3";
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "impl test 2.4";
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "impl test 2.5";
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "impl test 2.6";
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "impl test 2.7";
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "impl test 2.8";
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "impl test 2.9";

  // Test 3
  r := DominoOnWindowsill(5, 3, 4, 2, 1);
  expect r == true, "impl test 3";

  // Test 4
  r := DominoOnWindowsill(10, 10, 10, 5, 5);
  expect r == false, "impl test 4";

  // Test 5
  r := DominoOnWindowsill(1, 0, 0, 0, 0);
  expect r == true, "impl test 5";

  // Test 6
  r := DominoOnWindowsill(3, 3, 3, 3, 0);
  expect r == true, "impl test 6";

  // Test 7
  r := DominoOnWindowsill(6, 0, 0, 0, 6);
  expect r == true, "impl test 7";

  // Test 8 (3 cases)
  r := DominoOnWindowsill(4, 2, 3, 1, 2);
  expect r == false, "impl test 8.1";
  r := DominoOnWindowsill(5, 5, 5, 5, 0);
  expect r == true, "impl test 8.2";
  r := DominoOnWindowsill(3, 1, 1, 0, 2);
  expect r == true, "impl test 8.3";

  // Test 9
  r := DominoOnWindowsill(50, 25, 30, 10, 8);
  expect r == true, "impl test 9";

  // Test 10
  r := DominoOnWindowsill(7, 7, 0, 3, 3);
  expect r == true, "impl test 10";

  // Test 11 (2 cases)
  r := DominoOnWindowsill(10, 5, 5, 5, 5);
  expect r == true, "impl test 11.1";
  r := DominoOnWindowsill(8, 4, 6, 2, 3);
  expect r == true, "impl test 11.2";

  // Test 12
  r := DominoOnWindowsill(2, 1, 0, 0, 1);
  expect r == true, "impl test 12";

  print "All tests passed\n";
}