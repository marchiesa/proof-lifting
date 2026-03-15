// Find Equilibrium Index -- Spec tests

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
  var k := 0;
  while k < |a| decreases |a| - k {
    totalSum := totalSum + a[k];
    k := k + 1;
  }
  var leftSum := 0;
  var i := 0;
  while i < |a| decreases |a| - i {
    var rightSum := totalSum - leftSum - a[i];
    if leftSum == rightSum {
      assume {:axiom} IsEquilibrium(a, i);
      return i;
    }
    leftSum := leftSum + a[i];
    i := i + 1;
  }
  assume {:axiom} NoEquilibrium(a);
  return -1;
}

method Main() {
  // [1, 3, 5, 2, 2]: idx=2, left=[1,3]=4, right=[2,2]=4
  var a1 := [1, 3, 5, 2, 2];
  var r1 := FindEquilibrium(a1);
  expect r1 == 2;
  expect IsEquilibrium(a1, 2);

  // [-1, 3, -4, 5, 1, -6, 2, 1]: idx=1
  var a2 := [-1, 3, -4, 5, 1, -6, 2, 1];
  var r2 := FindEquilibrium(a2);
  expect r2 != -1;
  expect IsEquilibrium(a2, r2);

  // No equilibrium
  var a3 := [1, 2, 3];
  var r3 := FindEquilibrium(a3);
  expect r3 == -1;

  // Negative: [1,2,3] has no equilibrium
  expect !IsEquilibrium(a3, 0);
  expect !IsEquilibrium(a3, 1);
  expect !IsEquilibrium(a3, 2);

  // Single element: always equilibrium
  var a4 := [42];
  var r4 := FindEquilibrium(a4);
  expect r4 == 0;

  print "All spec tests passed\n";
}
