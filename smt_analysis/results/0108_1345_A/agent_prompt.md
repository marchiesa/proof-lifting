Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Puzzle Pieces
You are given a special jigsaw puzzle consisting of $$$n\cdot m$$$ identical pieces. Every piece has three tabs and one blank, as pictured below.

The jigsaw puzzle is considered solved if the following conditions hold:

1. The pieces are arranged into a grid with $$$n$$$ rows and $$$m$$$ columns.
2. For any two pieces that share an edge in the grid, a tab of one piece fits perfectly into a blank of the other piece.

Through rotation and translation of the pieces, determine if it is possible to solve the jigsaw puzzle.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0108_1345_A/task.dfy

```dafny
/*
 * Formal specification for the Puzzle Pieces problem.
 *
 * Model: An n×m grid where each cell holds an identical piece with 3 tabs
 * and 1 blank. An orientation in {0,1,2,3} determines which direction
 * (Up/Right/Down/Left) the blank faces. For every pair of adjacent cells,
 * exactly one shared side must be blank and the other must be a tab.
 */

// Orientation encoding: 0=Up, 1=Right, 2=Down, 3=Left.
// Returns true iff the side of a piece facing 'direction' is the blank.
ghost function SideIsBlank(orientation: int, direction: int): bool
{
  orientation == direction
}

// A valid configuration assigns an orientation in {0..3} to each of n*m cells.
ghost predicate ValidConfig(config: seq<int>, n: int, m: int)
  requires n >= 1 && m >= 1
{
  |config| == n * m &&
  (forall i | 0 <= i < n * m :: 0 <= config[i] <= 3)
}

// For every horizontal internal edge (between (r,c) and (r,c+1)):
// exactly one of the two facing sides is blank.
ghost predicate HorizEdgesOk(config: seq<int>, n: int, m: int)
  requires n >= 1 && m >= 1 && |config| == n * m
{
  forall r, c | 0 <= r < n && 0 <= c < m - 1 ::
    SideIsBlank(config[r * m + c], 1) != SideIsBlank(config[r * m + (c + 1)], 3)
}

// For every vertical internal edge (between (r,c) and (r+1,c)):
// exactly one of the two facing sides is blank.
ghost predicate VertEdgesOk(config: seq<int>, n: int, m: int)
  requires n >= 1 && m >= 1 && |config| == n * m
{
  forall r, c | 0 <= r < n - 1 && 0 <= c < m ::
    SideIsBlank(config[r * m + c], 2) != SideIsBlank(config[(r + 1) * m + c], 0)
}

// A configuration solves the n×m puzzle: valid orientations, all edges satisfied.
ghost predicate IsSolution(config: seq<int>, n: int, m: int)
  requires n >= 1 && m >= 1
{
  ValidConfig(config, n, m) &&
  HorizEdgesOk(config, n, m) &&
  VertEdgesOk(config, n, m)
}

// Exhaustive search over all orientation assignments: does any completion
// of 'partial' to length n*m form a valid solution?
// At each unfilled cell, tries all 4 orientations {0,1,2,3}.
ghost predicate HasSolutionFrom(n: int, m: int, partial: seq<int>)
  requires n >= 1 && m >= 1 && |partial| <= n * m
  decreases n * m - |partial|
{
  if |partial| == n * m then
    IsSolution(partial, n, m)
  else
    exists o | 0 <= o <= 3 :: HasSolutionFrom(n, m, partial + [o])
}

// The n×m puzzle is solvable: there exists an assignment of orientations
// to the n*m cells such that every internal edge has one blank and one tab.
ghost predicate PuzzleSolvable(n: int, m: int)
  requires n >= 1 && m >= 1
{
  HasSolutionFrom(n, m, [])
}

method PuzzlePieces(n: int, m: int) returns (result: bool)
  requires n >= 1 && m >= 1
  ensures result == PuzzleSolvable(n, m)
{
  result := n == 1 || m == 1 || (n == 2 && m == 2);
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0108_1345_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0108_1345_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0108_1345_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0108_1345_A/ (create the directory if needed).
