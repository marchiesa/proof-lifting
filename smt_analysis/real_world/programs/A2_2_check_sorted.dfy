// Pattern: Check if array is sorted
// Source: various sorting utilities, data processing pipelines
// Real-world: binary search precondition, merge validation, time series

predicate Sorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method IsSorted(a: seq<int>) returns (sorted: bool)
  ensures sorted <==> Sorted(a)
{
  if |a| <= 1 {
    sorted := true;
    return;
  }
  sorted := true;
  var i := 0;
  while i < |a| - 1
    invariant 0 <= i <= |a| - 1
    invariant sorted <==> Sorted(a[..i+1])
  {
    if a[i] > a[i + 1] {
      assert a[..i+2] == a[..i+1] + [a[i+1]];  // SMT QUIRK: B1 extensionality
      assert !Sorted(a[..i+2]);  // SMT QUIRK: A2 predicate instantiation
      sorted := false;
      // Need to show !Sorted(a) from !Sorted(a[..i+2])
      assert a[..i+2] == a[..|a|][..i+2];  // SMT QUIRK: subsequence reasoning
      return;
    }
    assert a[..i+2] == a[..i+1] + [a[i+1]];  // SMT QUIRK: B1 extensionality
    i := i + 1;
  }
  assert a[..|a|] == a;  // SMT QUIRK: B1 take-full
}
