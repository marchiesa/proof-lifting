// Find Equilibrium Index (left sum == right sum)
// Task: Add loop invariants so that Dafny can verify this program.

function SumRange(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else a[lo] + SumRange(a, lo + 1, hi)
}

predicate IsEquilibrium(a: seq<int>, idx: int) {
  0 <= idx < |a| &&
  SumRange(a, 0, idx) == SumRange(a, idx + 1, |a|)
}

predicate NoEquilibrium(a: seq<int>) {
  forall i :: 0 <= i < |a| ==> !IsEquilibrium(a, i)
}

method FindEquilibrium(a: seq<int>) returns (idx: int)
  ensures idx == -1 ==> NoEquilibrium(a)
  ensures idx != -1 ==> IsEquilibrium(a, idx)
{
  var totalSum := 0;
  var i := 0;
  while i < |a|
  {
    totalSum := totalSum + a[i];
    i := i + 1;
  }

  var leftSum := 0;
  i := 0;
  while i < |a|
  {
    var rightSum := totalSum - leftSum - a[i];
    if leftSum == rightSum {
      return i;
    }
    leftSum := leftSum + a[i];
    i := i + 1;
  }
  return -1;
}
