// Pattern: Convert 2D coordinates to linear index
// Source: various matrix/grid libraries
// Real-world: image processing, grid-based games, sparse matrix

method GridToLinear(row: int, col: int, numCols: int) returns (idx: int)
  requires row >= 0 && col >= 0 && numCols > 0
  requires col < numCols
  ensures idx >= 0
  ensures idx == row * numCols + col
{
  idx := row * numCols + col;
  assert row * numCols >= 0;  // SMT QUIRK: C1 NLA — needs hint for non-negative product
}
