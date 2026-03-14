// Remove Duplicates from Sorted Array (In-Place) -- Reference solution with invariants

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
  ghost var orig := a[..];
  ghost var wmap: seq<nat> := [0];
  ghost var result: seq<int> := [a[0]];
  var w: nat := 1;
  var r: nat := 1;
  while r < a.Length
    invariant 1 <= w <= r <= a.Length
    invariant |result| == w
    invariant |wmap| == r
    invariant StrictlySorted(result)
    invariant forall i :: 0 <= i < w ==> a[i] == result[i]
    invariant forall i :: 0 <= i < w ==> result[i] in orig
    invariant result[w - 1] == orig[r - 1]
    invariant forall i :: r <= i < a.Length ==> a[i] == orig[i]
    invariant IsSorted(orig)
    invariant forall j :: 0 <= j < r ==> wmap[j] < w && result[wmap[j]] == orig[j]
    decreases a.Length - r
  {
    if a[r] != a[w - 1] {
      assert a[r] == orig[r];
      assert result[w - 1] == orig[r - 1];
      assert orig[r - 1] <= orig[r];
      assert result[w - 1] < a[r];
      result := result + [a[r]];
      wmap := wmap + [w];
      a[w] := a[r];
      w := w + 1;
    } else {
      assert a[r] == orig[r];
      assert orig[r] == result[w - 1];
      wmap := wmap + [w - 1];
    }
    r := r + 1;
  }
  // Now prove postcondition
  assert |wmap| == a.Length;
  assert forall j :: 0 <= j < a.Length ==> wmap[j] < w && result[wmap[j]] == orig[j];
  assert forall i :: 0 <= i < w ==> a[i] == result[i];
  // Use witness map to find index for each original element
  var idx := 0;
  while idx < a.Length
    invariant 0 <= idx <= a.Length
    invariant forall j :: 0 <= j < idx ==> exists i :: 0 <= i < w && a[i] == orig[j]
    decreases a.Length - idx
  {
    assert wmap[idx] < w;
    assert result[wmap[idx]] == orig[idx];
    assert a[wmap[idx]] == result[wmap[idx]];
    assert a[wmap[idx]] == orig[idx];
    idx := idx + 1;
  }
  return w;
}
