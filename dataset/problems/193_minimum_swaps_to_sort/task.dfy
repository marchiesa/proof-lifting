// Minimum Swaps to Sort
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsPermutation(a: seq<int>)
{
  (forall i :: 0 <= i < |a| ==> 0 <= a[i] < |a|) &&
  (forall i, j :: 0 <= i < j < |a| ==> a[i] != a[j])
}

predicate IsSorted(a: seq<int>)
{
  forall i :: 0 <= i < |a| ==> a[i] == i
}

method MinSwaps(a: seq<int>) returns (swaps: int)
  requires IsPermutation(a)
  ensures swaps >= 0
{
  var arr := a;
  swaps := 0;
  var i := 0;
  while i < |arr|
  {
    while arr[i] != i
    {
      var target := arr[i];
      var tmp := arr[i];
      arr := arr[..i] + [arr[target]] + arr[i+1..target] + [tmp] + arr[target+1..];
      swaps := swaps + 1;
    }
    i := i + 1;
  }
}
