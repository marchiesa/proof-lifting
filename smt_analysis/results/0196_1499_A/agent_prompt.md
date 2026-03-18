Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Domino on Windowsill
You have a board represented as a grid with $$$2 \times n$$$ cells.

The first $$$k_1$$$ cells on the first row and first $$$k_2$$$ cells on the second row are colored in white. All other cells are colored in black.

You have $$$w$$$ white dominoes ($$$2 \times 1$$$ tiles, both cells are colored in white) and $$$b$$$ black dominoes ($$$2 \times 1$$$ tiles, both cells are colored in black).

You can place a white domino on the board if both board's cells are white and not occupied by any other domino. In the same way, you can place a black domino if both cells are black and not occupied by any other domino.

Can you place all $$$w + b$$$ dominoes on the board if you can place dominoes both horizontally and vertically?

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0196_1499_A/task.dfy

```dafny
// A domino is represented by (row, col, horizontal)
// If horizontal: covers (row, col) and (row, col+1)
// If vertical: covers (0, col) and (1, col)

datatype Domino = Domino(row: int, col: int, horizontal: bool)

ghost function Cell1Row(d: Domino): int { d.row }
ghost function Cell1Col(d: Domino): int { d.col }
ghost function Cell2Row(d: Domino): int { if d.horizontal then d.row else 1 - d.row }
ghost function Cell2Col(d: Domino): int { if d.horizontal then d.col + 1 else d.col }

// A domino is on the board and geometrically valid
ghost predicate ValidDomino(d: Domino, n: int)
{
  n >= 0 &&
  if d.horizontal then
    (d.row == 0 || d.row == 1) && 0 <= d.col && d.col + 1 < n
  else
    d.row == 0 && 0 <= d.col && d.col < n
}

// Is a cell white? Row 0: columns 0..k1-1 are white. Row 1: columns 0..k2-1 are white.
ghost predicate CellIsWhite(row: int, col: int, k1: int, k2: int)
{
  (row == 0 && col < k1) || (row == 1 && col < k2)
}

// A domino is a white domino (covers two white cells)
ghost predicate IsWhiteDomino(d: Domino, k1: int, k2: int)
{
  CellIsWhite(Cell1Row(d), Cell1Col(d), k1, k2) &&
  CellIsWhite(Cell2Row(d), Cell2Col(d), k1, k2)
}

// A domino is a black domino (covers two black cells)
ghost predicate IsBlackDomino(d: Domino, n: int, k1: int, k2: int)
{
  !CellIsWhite(Cell1Row(d), Cell1Col(d), k1, k2) &&
  !CellIsWhite(Cell2Row(d), Cell2Col(d), k1, k2)
}

// Two dominoes overlap if they share a cell
ghost predicate DominoesOverlap(d1: Domino, d2: Domino)
{
  var r1a := Cell1Row(d1); var c1a := Cell1Col(d1);
  var r1b := Cell2Row(d1); var c1b := Cell2Col(d1);
  var r2a := Cell1Row(d2); var c2a := Cell1Col(d2);
  var r2b := Cell2Row(d2); var c2b := Cell2Col(d2);
  (r1a == r2a && c1a == c2a) || (r1a == r2b && c1a == c2b) ||
  (r1b == r2a && c1b == c2a) || (r1b == r2b && c1b == c2b)
}

// No two dominoes in the placement overlap
ghost predicate NoOverlaps(placement: seq<Domino>)
{
  forall i, j | 0 <= i < |placement| && 0 <= j < |placement| && i != j ::
    !DominoesOverlap(placement[i], placement[j])
}

// Count white dominoes in a placement
ghost function CountWhite(placement: seq<Domino>, k1: int, k2: int): int
  decreases |placement|
{
  if |placement| == 0 then 0
  else
    (if IsWhiteDomino(placement[|placement|-1], k1, k2) then 1 else 0) +
    CountWhite(placement[..|placement|-1], k1, k2)
}

// Count black dominoes in a placement
ghost function CountBlack(placement: seq<Domino>, n: int, k1: int, k2: int): int
  decreases |placement|
{
  if |placement| == 0 then 0
  else
    (if IsBlackDomino(placement[|placement|-1], n, k1, k2) then 1 else 0) +
    CountBlack(placement[..|placement|-1], n, k1, k2)
}

// Every domino is valid and is either white or black (no mixed-color dominoes)
ghost predicate AllDominoesValid(placement: seq<Domino>, n: int, k1: int, k2: int)
{
  forall i | 0 <= i < |placement| ::
    ValidDomino(placement[i], n) &&
    (IsWhiteDomino(placement[i], k1, k2) || IsBlackDomino(placement[i], n, k1, k2))
}

// A valid placement of exactly w white and b black dominoes on the 2×n board
ghost predicate ValidPlacement(placement: seq<Domino>, n: int, k1: int, k2: int, w: int, b: int)
{
  |placement| == w + b &&
  AllDominoesValid(placement, n, k1, k2) &&
  NoOverlaps(placement) &&
  CountWhite(placement, k1, k2) == w &&
  CountBlack(placement, n, k1, k2) == b
}

// There exists a valid placement — we bound the search by enumerating over
// all possible sequences of dominoes of length w+b.
// Each domino has row in {0,1}, col in {0..n-1}, horizontal in {false, true},
// so we enumerate via integer encoding.
// Encoding: a domino is encoded as an int e in [0, 4*n):
//   col = e / 4, row = (e / 2) % 2, horizontal = (e % 2) == 1

ghost function DecodeDomino(e: int): Domino
{
  Domino((e / 2) % 2, e / 4, (e % 2) == 1)
}

// Build a placement from a sequence of encoded ints
ghost function BuildPlacement(encoding: seq<int>): seq<Domino>
  decreases |encoding|
{
  if |encoding| == 0 then []
  else BuildPlacement(encoding[..|encoding|-1]) + [DecodeDomino(encoding[|encoding|-1])]
}

// Check if a placement encoded by a sequence of ints (each in [0, 4*n)) is valid
ghost predicate ValidEncodedPlacement(encoding: seq<int>, n: int, k1: int, k2: int, w: int, b: int)
{
  |encoding| == w + b &&
  (forall i | 0 <= i < |encoding| :: 0 <= encoding[i] < 4 * n) &&
  ValidPlacement(BuildPlacement(encoding), n, k1, k2, w, b)
}

// Existential check: there exists a valid placement
ghost predicate CanPlace(n: int, k1: int, k2: int, w: int, b: int)
  requires n >= 1
  requires 0 <= k1 <= n && 0 <= k2 <= n
  requires w >= 0 && b >= 0
{
  exists placement: seq<Domino> :: ValidPlacement(placement, n, k1, k2, w, b)
}

// Recursively enumerate all encoded placements of length 'remaining'
// partial is the encoding built so far
ghost predicate ExistsPlacement(partial: seq<int>, remaining: int, domainSize: int,
                          n: int, k1: int, k2: int, w: int, b: int)
  requires domainSize >= 0
  requires remaining >= 0
  decreases remaining
{
  if remaining == 0 then
    ValidEncodedPlacement(partial, n, k1, k2, w, b)
  else
    exists e ::
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
```

## Instructions:

1. Read the code carefully. Understand what the method does and what the spec requires.

2. Add loop invariants for every loop. Common patterns:
   - Bounds: `invariant 0 <= i <= |s|`
   - Accumulator: `invariant acc == F(s[..i])` for recursive ghost functions
   - Sequence slicing: `assert s[..i+1] == s[..i] + [s[i]];` before using F(s[..i+1])
   - Full slice identity: `assert s[..|s|] == s;` after loops that process entire sequences
   - Type preservation: `invariant AllNonNeg(s[..i])` if needed by the spec

3. Add helper lemmas if needed (e.g., SumAppend, induction lemmas).

4. Run dafny verify:
   ```bash
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0196_1499_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0196_1499_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0196_1499_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0196_1499_A/ (create the directory if needed).
