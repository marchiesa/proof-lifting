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