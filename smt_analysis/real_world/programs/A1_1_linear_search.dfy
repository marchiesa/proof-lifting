// Pattern: Linear search for first element matching condition
// Source: imcut/__ordered_values_by_indexes (find values by index)
//         qpimage/find_sideband (find sideband in FFT)
// Real-world: database lookup, UI element finding, config key search

method LinearSearch(a: seq<int>, target: int) returns (found: bool, idx: int)
  ensures found ==> 0 <= idx < |a| && a[idx] == target
  ensures !found ==> forall i :: 0 <= i < |a| ==> a[i] != target
{
  found := false;
  idx := -1;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant !found ==> forall j :: 0 <= j < i ==> a[j] != target
    invariant found ==> 0 <= idx < |a| && a[idx] == target
  {
    if a[i] == target {
      assert a[i] == target;  // SMT QUIRK: A1 existential witness
      found := true;
      idx := i;
      return;
    }
    i := i + 1;
  }
}
