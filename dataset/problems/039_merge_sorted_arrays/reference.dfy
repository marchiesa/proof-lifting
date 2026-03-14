// Merge Two Sorted Arrays Into One Sorted Array -- Reference solution with invariants

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method MergeArrays(a: array<int>, b: array<int>) returns (c: array<int>)
  requires IsSorted(a[..])
  requires IsSorted(b[..])
  ensures IsSorted(c[..])
  ensures c.Length == a.Length + b.Length
  ensures multiset(c[..]) == multiset(a[..]) + multiset(b[..])
{
  c := new int[a.Length + b.Length];
  var i := 0;
  var j := 0;
  var k := 0;
  while k < c.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= j <= b.Length
    invariant k == i + j
    invariant k <= c.Length
    invariant IsSorted(c[..k])
    invariant multiset(c[..k]) == multiset(a[..i]) + multiset(b[..j])
    invariant k > 0 && i < a.Length ==> c[k - 1] <= a[i]
    invariant k > 0 && j < b.Length ==> c[k - 1] <= b[j]
    decreases c.Length - k
  {
    if i < a.Length && (j >= b.Length || a[i] <= b[j]) {
      c[k] := a[i];
      assert a[..i+1] == a[..i] + [a[i]];
      i := i + 1;
    } else {
      c[k] := b[j];
      assert b[..j+1] == b[..j] + [b[j]];
      j := j + 1;
    }
    assert c[..k+1] == c[..k] + [c[k]];
    k := k + 1;
  }
  assert a[..a.Length] == a[..];
  assert b[..b.Length] == b[..];
  assert c[..c.Length] == c[..];
}
