// Counting Inversions
// Task: Add loop invariants so that Dafny can verify this program.
// Count the number of inversions in a sequence (pairs i < j with a[i] > a[j]).

function InvFrom(a: seq<int>, i: int, j: int): int
  requires 0 <= i < |a|
  requires i < j
  decreases |a| - j
{
  if j >= |a| then 0
  else (if a[i] > a[j] then 1 else 0) + InvFrom(a, i, j + 1)
}

function TotalInv(a: seq<int>, i: int): int
  requires 0 <= i
  decreases |a| - i
{
  if i >= |a| then 0
  else if i + 1 >= |a| then 0
  else InvFrom(a, i, i + 1) + TotalInv(a, i + 1)
}

method CountInversions(a: seq<int>) returns (count: int)
  ensures count == TotalInv(a, 0)
{
  count := 0;
  var i := 0;
  while i < |a|
  {
    var j := i + 1;
    while j < |a|
    {
      if a[i] > a[j] {
        count := count + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
