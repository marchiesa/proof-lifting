// Merge Sort
// Task: Add loop invariants so that Dafny can verify this program.

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
  {
    if i < |a| && (j >= |b| || a[i] <= b[j]) {
      r := r + [a[i]];
      i := i + 1;
    } else {
      r := r + [b[j]];
      j := j + 1;
    }
  }
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
