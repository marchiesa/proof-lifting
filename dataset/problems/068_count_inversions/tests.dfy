// Count Inversions -- Test cases

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

method {:axiom} CountInversions(a: seq<int>) returns (count: int)
  ensures count == TotalInversions(a)

method TestSorted()
{
  var c := CountInversions([1, 2, 3]);
  assert TotalInversions([1, 2, 3]) == 0;
  assert c == 0;
}

method TestReversed()
{
  var c := CountInversions([3, 2, 1]);
  assert TotalInversions([3, 2, 1]) == 3;
  assert c == 3;
}

method TestSingleInversion()
{
  var c := CountInversions([2, 1]);
  assert TotalInversions([2, 1]) == 1;
  assert c == 1;
}
