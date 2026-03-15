// Maximum Sum Rectangle in 2D Matrix
// Task: Add loop invariants so that Dafny can verify this program.

function RectSum(m: seq<seq<int>>, r1: int, c1: int, r2: int, c2: int): int
  requires 0 <= r1 <= r2 <= |m|
  requires forall i :: 0 <= i < |m| ==> 0 <= c1 <= c2 <= |m[i]|
  decreases r2 - r1
{
  if r1 == r2 then 0
  else RowSum(m[r1], c1, c2) + RectSum(m, r1 + 1, c1, r2, c2)
}

function RowSum(row: seq<int>, c1: int, c2: int): int
  requires 0 <= c1 <= c2 <= |row|
  decreases c2 - c1
{
  if c1 == c2 then 0
  else row[c1] + RowSum(row, c1 + 1, c2)
}

method MaxSumRectangle(m: seq<seq<int>>, rows: int, cols: int) returns (maxSum: int)
  requires rows > 0 && cols > 0
  requires |m| == rows
  requires forall i :: 0 <= i < rows ==> |m[i]| == cols
  ensures maxSum >= m[0][0]
{
  maxSum := m[0][0];
  var r1 := 0;
  while r1 < rows
  {
    var r2 := r1 + 1;
    while r2 <= rows
    {
      var c1 := 0;
      while c1 < cols
      {
        var c2 := c1 + 1;
        while c2 <= cols
        {
          var s := RectSum(m, r1, c1, r2, c2);
          if s > maxSum {
            maxSum := s;
          }
          c2 := c2 + 1;
        }
        c1 := c1 + 1;
      }
      r2 := r2 + 1;
    }
    r1 := r1 + 1;
  }
}
