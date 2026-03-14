// Merge Sort -- Reference solution with invariants

predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method Merge(a: seq<int>, b: seq<int>) returns (r: seq<int>)
  requires IsSorted(a) && IsSorted(b)
  ensures IsSorted(r)
  ensures multiset(r) == multiset(a) + multiset(b)
{
  r := [];
  var i := 0;
  var j := 0;
  while i < |a| || j < |b|
    invariant 0 <= i <= |a|
    invariant 0 <= j <= |b|
    invariant IsSorted(r)
    invariant multiset(r) == multiset(a[..i]) + multiset(b[..j])
    invariant |r| > 0 && i < |a| ==> r[|r| - 1] <= a[i]
    invariant |r| > 0 && j < |b| ==> r[|r| - 1] <= b[j]
    decreases |a| - i + |b| - j
  {
    if i < |a| && (j >= |b| || a[i] <= b[j]) {
      assert a[..i+1] == a[..i] + [a[i]];
      r := r + [a[i]];
      i := i + 1;
    } else {
      assert b[..j+1] == b[..j] + [b[j]];
      r := r + [b[j]];
      j := j + 1;
    }
  }
  assert a[..i] == a;
  assert b[..j] == b;
}

method MergeSort(s: seq<int>) returns (r: seq<int>)
  ensures IsSorted(r)
  ensures multiset(r) == multiset(s)
  decreases |s|
{
  if |s| <= 1 {
    return s;
  }
  var mid := |s| / 2;
  var left := MergeSort(s[..mid]);
  var right := MergeSort(s[mid..]);
  assert multiset(s) == multiset(s[..mid]) + multiset(s[mid..]) by {
    assert s == s[..mid] + s[mid..];
  }
  r := Merge(left, right);
}
