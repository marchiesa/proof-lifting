// Pattern: Find maximum element in array
// Source: commah/acc_rate (find peak accretion rate)
//         various numerical computing libraries
// Real-world: statistics, scoring, resource allocation

method FindMax(a: seq<int>) returns (maxVal: int)
  requires |a| > 0
  ensures maxVal in a
  ensures forall i :: 0 <= i < |a| ==> a[i] <= maxVal
{
  maxVal := a[0];
  var i := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant maxVal in a[..i]
    invariant forall j :: 0 <= j < i ==> a[j] <= maxVal
  {
    if a[i] > maxVal {
      maxVal := a[i];
    }
    assert maxVal in a[..i+1];  // SMT QUIRK: A1 existential witness (maxVal exists in prefix)
    i := i + 1;
  }
  assert a[..|a|] == a;  // SMT QUIRK: B1 take-full
}
