// Pascal's Triangle Row -- Test cases

function Choose(n: nat, k: nat): nat
  decreases n, k
{
  if k == 0 then 1
  else if n == 0 then 0
  else Choose(n-1, k-1) + Choose(n-1, k)
}

function PascalRow(n: nat): seq<nat>
{
  seq(n + 1, k requires 0 <= k <= n => Choose(n, k))
}

method {:axiom} ComputePascalRow(n: nat) returns (row: seq<nat>)
  ensures row == PascalRow(n)

method TestRow0()
{
  var r := ComputePascalRow(0);
  assert |r| == 1;
  assert r[0] == Choose(0, 0) == 1;
}

method TestRow1()
{
  var r := ComputePascalRow(1);
  assert |r| == 2;
}

method TestRow4()
{
  var r := ComputePascalRow(4);
  assert |r| == 5;
  assert r[0] == Choose(4, 0) == 1;
}
