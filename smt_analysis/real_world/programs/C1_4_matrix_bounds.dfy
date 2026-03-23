// Pattern: Compute linear index from 2D coordinates with bounds proof
// Source: image processing, game grids, spreadsheet computations
// Real-world: bounds checking for 2D array stored linearly

lemma ProductMonotone(a: int, b: int, c: int)
  requires 0 <= a < b
  requires c > 0
  ensures a * c < b * c
{
  // SMT QUIRK: C1 NLA — Z3 cannot prove a*c < b*c automatically
}

method LinearizeGrid(rows: int, cols: int) returns (indices: seq<int>)
  requires rows > 0 && cols > 0
  ensures |indices| == rows
  ensures forall k :: 0 <= k < rows ==> indices[k] == k * cols
  ensures forall k :: 0 <= k < rows ==> 0 <= indices[k] < rows * cols
{
  indices := [];
  var k := 0;
  while k < rows
    invariant 0 <= k <= rows
    invariant |indices| == k
    invariant forall j :: 0 <= j < k ==> indices[j] == j * cols
    invariant forall j :: 0 <= j < k ==> 0 <= indices[j] < rows * cols
  {
    ProductMonotone(k, rows, cols);  // SMT QUIRK: C1 NLA — need lemma for k*cols < rows*cols
    indices := indices + [k * cols];
    k := k + 1;
  }
}
