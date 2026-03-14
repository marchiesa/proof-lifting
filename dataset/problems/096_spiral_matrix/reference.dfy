// Flatten Matrix (row-major order) -- Reference solution with invariants

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
    FlattenLength(m[1..], rows - 1, cols);
  }
}

lemma FlattenAppendRow(m: seq<seq<int>>, row: seq<int>)
  ensures FlattenSpec(m + [row]) == FlattenSpec(m) + row
  decreases |m|
{
  if |m| == 0 {
    assert m + [row] == [row];
    assert FlattenSpec([row]) == row + FlattenSpec([row][1..]);
    var empty: seq<seq<int>> := [];
    assert [row][1..] == empty;
  } else {
    assert (m + [row])[0] == m[0];
    assert (m + [row])[1..] == m[1..] + [row];
    FlattenAppendRow(m[1..], row);
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
    invariant 0 <= i <= rows
    invariant result == FlattenSpec(m[..i])
    decreases rows - i
  {
    var j := 0;
    var rowResult: seq<int> := [];
    while j < cols
      invariant 0 <= j <= cols
      invariant rowResult == m[i][..j]
      decreases cols - j
    {
      rowResult := rowResult + [m[i][j]];
      j := j + 1;
    }
    assert rowResult == m[i];
    FlattenAppendRow(m[..i], m[i]);
    assert m[..i] + [m[i]] == m[..i+1];
    result := result + rowResult;
    i := i + 1;
  }
  assert m[..rows] == m;
}
