method matrixCount(rows: int, cols: int) returns (count: int)
  requires rows >= 0
  requires cols >= 0
  ensures count == rows * cols
{
  count := 0;
  var i := 0;
  while i < rows
    invariant 0 <= i <= rows
    invariant count == i * cols
  {
    var j := 0;
    while j < cols
      invariant 0 <= j <= cols
      invariant count == i * cols + j
    {
      count := count + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}
