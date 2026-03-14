// Pascal's Triangle Row Computation
// Task: Add loop invariants so that Dafny can verify this program.

// Binomial coefficient C(n, k)
function Choose(n: nat, k: nat): nat
  decreases n, k
{
  if k == 0 then 1
  else if n == 0 then 0
  else Choose(n-1, k-1) + Choose(n-1, k)
}

// The nth row of Pascal's triangle
function PascalRow(n: nat): seq<nat>
{
  seq(n + 1, k requires 0 <= k <= n => Choose(n, k))
}

method ComputePascalRow(n: nat) returns (row: seq<nat>)
  ensures row == PascalRow(n)
{
  row := [1];
  var i: nat := 1;
  while i <= n
  {
    var newRow: seq<nat> := [1];
    var j: nat := 1;
    while j < i
    {
      newRow := newRow + [row[j-1] + row[j]];
      j := j + 1;
    }
    newRow := newRow + [1];
    row := newRow;
    i := i + 1;
  }
}
