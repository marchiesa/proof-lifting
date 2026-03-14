// Three Sum: Find triple summing to target
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method ThreeSum(a: seq<int>, target: int) returns (found: bool, i: int, j: int, k: int)
  requires IsSorted(a)
  ensures found ==> 0 <= i < j < k < |a| && a[i] + a[j] + a[k] == target
  ensures !found ==> forall p, q, r :: 0 <= p < q < r < |a| ==> a[p] + a[q] + a[r] != target
{
  found := false;
  i := 0; j := 0; k := 0;
  var idx := 0;
  while idx < |a|
  {
    var lo := idx + 1;
    var hi := |a| - 1;
    while lo < hi
    {
      var s := a[idx] + a[lo] + a[hi];
      if s == target {
        found := true;
        i := idx;
        j := lo;
        k := hi;
        return;
      } else if s < target {
        lo := lo + 1;
      } else {
        hi := hi - 1;
      }
    }
    idx := idx + 1;
  }
}
