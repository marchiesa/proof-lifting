// Zigzag Traversal
// Task: Add loop invariants so that Dafny can verify this program.
// Traverse a matrix row by row, reversing every other row.

predicate IsRectangular(m: seq<seq<int>>, rows: int, cols: int)
{
  |m| == rows && forall i :: 0 <= i < rows ==> |m[i]| == cols
}

function ZigzagSpec(m: seq<seq<int>>, rows: int, cols: int): seq<int>
  requires IsRectangular(m, rows, cols)
  requires rows >= 0 && cols >= 0
  decreases rows
{
  if rows == 0 then []
  else
    var firstRow := if rows % 2 == 1 then m[0] else Reverse(m[0]);
    firstRow + ZigzagSpec(m[1..], rows - 1, cols)
}

function Reverse(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else Reverse(s[1..]) + [s[0]]
}

method ZigzagTraversal(m: seq<seq<int>>, rows: int, cols: int) returns (result: seq<int>)
  requires rows >= 0 && cols >= 0
  requires IsRectangular(m, rows, cols)
  ensures |result| == rows * cols
{
  result := [];
  var i := 0;
  while i < rows
  {
    var j := 0;
    while j < cols
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
