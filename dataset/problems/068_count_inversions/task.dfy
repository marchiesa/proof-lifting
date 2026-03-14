// Count Inversions (O(n^2))
// Task: Add loop invariants so that Dafny can verify this program.

function InvCount(a: seq<int>, i: int, j: int): int
  requires 0 <= i <= |a|
  requires 0 <= j <= |a|
  decreases |a| - j
{
  if i >= |a| || j >= |a| then 0
  else if i >= j then 0
  else (if a[i] > a[j] then 1 else 0) + InvCount(a, i, j + 1)
}

function TotalInvFrom(a: seq<int>, i: int): int
  requires 0 <= i <= |a|
  decreases |a| - i
{
  if i >= |a| then 0
  else InvCount(a, i, i + 1) + TotalInvFrom(a, i + 1)
}

function TotalInversions(a: seq<int>): int
{
  TotalInvFrom(a, 0)
}

method CountInversions(a: seq<int>) returns (count: int)
  ensures count == TotalInversions(a)
{
  count := 0;
  var i := 0;
  while i < |a|
  {
    var j := i + 1;
    var rowInv := 0;
    while j < |a|
    {
      if a[i] > a[j] {
        rowInv := rowInv + 1;
      }
      j := j + 1;
    }
    count := count + rowInv;
    i := i + 1;
  }
}
