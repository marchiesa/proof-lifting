// Remove Duplicates from Sorted Array (In-Place)
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate StrictlySorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] < a[j]
}

method RemoveDuplicates(a: array<int>) returns (k: nat)
  requires IsSorted(a[..])
  modifies a
  ensures k <= a.Length
  ensures StrictlySorted(a[..k])
  ensures forall i :: 0 <= i < k ==> a[i] in old(a[..])
  ensures forall j :: 0 <= j < |old(a[..])| ==> exists i :: 0 <= i < k && a[i] == old(a[..])[j]
{
  if a.Length == 0 {
    return 0;
  }
  var w := 1;
  var r := 1;
  while r < a.Length
  {
    if a[r] != a[w - 1] {
      a[w] := a[r];
      w := w + 1;
    }
    r := r + 1;
  }
  return w;
}
