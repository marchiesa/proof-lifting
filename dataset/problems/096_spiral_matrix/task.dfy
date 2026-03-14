// Flatten Matrix (row-major order)
// Task: Add loop invariants so that Dafny can verify this program.

predicate ValidMatrix(m: seq<seq<int>>, rows: int, cols: int)
{
  |m| == rows && rows >= 0 && cols >= 0 &&
  forall i :: 0 <= i < rows ==> |m[i]| == cols
}

function FlattenSpec(m: seq<seq<int>>): seq<int>
{
  if |m| == 0 then []
  else m[0] + FlattenSpec(m[1..])
}

lemma FlattenLength(m: seq<seq<int>>, rows: int, cols: int)
  requires ValidMatrix(m, rows, cols)
  ensures |FlattenSpec(m)| == rows * cols
  decreases rows
{
  if rows > 0 {
    assert m[1..] == m[1..];
    FlattenLength(m[1..], rows - 1, cols);
  }
}

method Flatten(m: seq<seq<int>>, rows: int, cols: int) returns (result: seq<int>)
  requires ValidMatrix(m, rows, cols)
  ensures result == FlattenSpec(m)
  ensures |result| == rows * cols
{
  FlattenLength(m, rows, cols);
  result := [];
  var i := 0;
  while i < rows
  {
    var j := 0;
    while j < cols
    {
      result := result + [m[i][j]];
      j := j + 1;
    }
    i := i + 1;
  }
}
