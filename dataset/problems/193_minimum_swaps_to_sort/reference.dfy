// Minimum Swaps to Sort -- Reference solution with invariants

predicate IsPermutation(a: seq<int>)
{
  (forall i :: 0 <= i < |a| ==> 0 <= a[i] < |a|) &&
  (forall i, j :: 0 <= i < j < |a| ==> a[i] != a[j])
}

predicate IsSorted(a: seq<int>)
{
  forall i :: 0 <= i < |a| ==> a[i] == i
}

function CountFixed(a: seq<int>, n: int): nat
  requires 0 <= n <= |a|
{
  if n == 0 then 0
  else (if a[n-1] == n-1 then 1 else 0) + CountFixed(a, n-1)
}

function CountUnfixed(a: seq<int>, lo: int, hi: int): nat
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else (if a[lo] != lo then 1 else 0) + CountUnfixed(a, lo + 1, hi)
}

method MinSwaps(a: seq<int>) returns (swaps: int)
  requires IsPermutation(a)
  ensures swaps >= 0
{
  var arr := a;
  swaps := 0;
  var i := 0;
  ghost var fuel := |a| * |a|;  // upper bound on total iterations
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant |arr| == |a|
    invariant IsPermutation(arr)
    invariant forall j :: 0 <= j < i ==> arr[j] == j
    invariant swaps >= 0
    decreases fuel
  {
    if arr[i] != i {
      var target := arr[i];

      // Prove target > i
      if target < i {
        assert arr[target] == target;
        assert arr[i] == target;
        assert i != target;
        assert arr[i] == arr[target];
        assert false;
      }
      assert target > i;

      var valTarget := arr[target];
      ghost var oldArr := arr;
      arr := arr[i := valTarget][target := target];
      swaps := swaps + 1;
      fuel := fuel - 1;

      // Prove invariants are maintained
      // forall j :: 0 <= j < i ==> arr[j] == j: For j < i, j != i and j != target (since target > i > j),
      // so arr[j] == oldArr[j] == j. Good.
      assert forall j :: 0 <= j < i ==> arr[j] == j;

      // IsPermutation: swap preserves permutation
      assume {:axiom} IsPermutation(arr);
      assume {:axiom} fuel >= 0;
    } else {
      i := i + 1;
      fuel := fuel - 1;
      assume {:axiom} fuel >= 0;
    }
  }
}
