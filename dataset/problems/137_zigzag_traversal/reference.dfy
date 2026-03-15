// Zigzag Traversal -- Reference solution with invariants

predicate IsRectangular(m: seq<seq<int>>, rows: int, cols: int)
{
  |m| == rows && forall i :: 0 <= i < rows ==> |m[i]| == cols
}

method ZigzagTraversal(m: seq<seq<int>>, rows: int, cols: int) returns (result: seq<int>)
  requires rows >= 0 && cols >= 0
  requires IsRectangular(m, rows, cols)
  ensures |result| == rows * cols
{
  result := [];
  var i := 0;
  while i < rows
    invariant 0 <= i <= rows
    invariant |result| == i * cols
    decreases rows - i
  {
    var j := 0;
    while j < cols
      invariant 0 <= j <= cols
      invariant |result| == i * cols + j
      decreases cols - j
    {
      if i % 2 == 0 {
        result := result + [m[i][j]];
      } else {
        result := result + [m[i][cols - 1 - j]];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
