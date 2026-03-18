Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Game of Life
William really likes the cellular automaton called "Game of Life" so he decided to make his own version. For simplicity, William decided to define his cellular automaton on an array containing $$$n$$$ cells, with each cell either being alive or dead.

Evolution of the array in William's cellular automaton occurs iteratively in the following way:

- If the element is dead and it has exactly $$$1$$$ alive neighbor in the current state of the array, then on the next iteration it will become alive. For an element at index $$$i$$$ the neighbors would be elements with indices $$$i - 1$$$ and $$$i + 1$$$. If there is no element at that index, it is considered to be a dead neighbor.
- William is a humane person so all alive elements stay alive.

Check the note section for examples of the evolution.

You are given some initial state of all elements and you need to help William find the state of the array after $$$m$$$ iterations of evolution.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0210_1523_A/task.dfy

```dafny
// --- Formal specification: models the 1D cellular automaton evolution ---

// Count of alive (==1) neighbors for cell at index i
ghost function CountAliveNeighbors(cells: seq<int>, i: int): int
  requires 0 <= i < |cells|
{
  (if i > 0 && cells[i - 1] == 1 then 1 else 0) +
  (if i < |cells| - 1 && cells[i + 1] == 1 then 1 else 0)
}

// Next state of a single cell after one evolution step
ghost function CellNextState(cells: seq<int>, i: int): int
  requires 0 <= i < |cells|
{
  if cells[i] == 1 then 1                                // alive stays alive
  else if CountAliveNeighbors(cells, i) == 1 then 1      // dead with exactly 1 alive neighbor → alive
  else 0                                                  // otherwise stays dead
}

// Build the first k cells of the evolved array (references original cells for neighbors)
ghost function BuildEvolved(cells: seq<int>, k: int): seq<int>
  requires 0 <= k <= |cells|
  ensures |BuildEvolved(cells, k)| == k
  decreases k
{
  if k == 0 then []
  else BuildEvolved(cells, k - 1) + [CellNextState(cells, k - 1)]
}

// One simultaneous evolution step applied to all cells
ghost function EvolveOnce(cells: seq<int>): seq<int>
  ensures |EvolveOnce(cells)| == |cells|
{
  BuildEvolved(cells, |cells|)
}

// State after m evolution steps (fixed-point shortcut is safe:
// if EvolveOnce(s)==s then EvolveOnce^k(s)==s for all k)
ghost function Evolve(cells: seq<int>, m: int): seq<int>
  requires m >= 0
  decreases m
{
  if m == 0 then cells
  else
    var next := EvolveOnce(cells);
    if next == cells then cells
    else Evolve(next, m - 1)
}

// All elements are 0 or 1
ghost predicate ValidCells(cells: seq<int>)
{
  forall i :: 0 <= i < |cells| ==> (cells[i] == 0 || cells[i] == 1)
}

// --- Method with formal specification ---

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

  // Compute left: index of nearest 1 at or to the left of each position
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

  // Compute right: index of nearest 1 at or to the right of each position
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

  // Compute result
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0210_1523_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0210_1523_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0210_1523_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0210_1523_A/ (create the directory if needed).
