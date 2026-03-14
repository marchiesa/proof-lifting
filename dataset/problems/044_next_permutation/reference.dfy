// Next Permutation (Lexicographic) -- Reference solution with invariants

predicate IsSortedDesc(a: array<int>, lo: int, hi: int)
  reads a
  requires 0 <= lo <= hi <= a.Length
{
  forall i, j :: lo <= i < j < hi ==> a[i] >= a[j]
}

method ReverseSubarray(a: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= a.Length
  modifies a
  ensures forall k :: lo <= k < hi ==> a[k] == old(a[lo + hi - 1 - k])
  ensures forall k :: 0 <= k < lo ==> a[k] == old(a[k])
  ensures forall k :: hi <= k < a.Length ==> a[k] == old(a[k])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var i := lo;
  var j := hi - 1;
  while i < j
    invariant lo <= i
    invariant lo > 0 || hi > 0 || i == lo
    invariant i <= j + 1
    invariant i + j == lo + hi - 1
    invariant forall k :: i <= k <= j ==> a[k] == old(a[k])
    invariant forall k :: lo <= k < i ==> a[k] == old(a[lo + hi - 1 - k])
    invariant forall k :: j < k < hi ==> a[k] == old(a[lo + hi - 1 - k])
    invariant forall k :: 0 <= k < lo ==> a[k] == old(a[k])
    invariant forall k :: hi <= k < a.Length ==> a[k] == old(a[k])
    invariant multiset(a[..]) == old(multiset(a[..]))
    decreases j - i
  {
    a[i], a[j] := a[j], a[i];
    i := i + 1;
    j := j - 1;
  }
}

method NextPermutation(a: array<int>) returns (found: bool)
  modifies a
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  if a.Length <= 1 {
    return false;
  }

  var i := a.Length - 2;
  while i >= 0 && a[i] >= a[i + 1]
    invariant -1 <= i <= a.Length - 2
    invariant IsSortedDesc(a, i + 1, a.Length)
    decreases i + 1
  {
    i := i - 1;
  }

  if i < 0 {
    ReverseSubarray(a, 0, a.Length);
    return false;
  }

  var j := a.Length - 1;
  while a[j] <= a[i]
    invariant i < j <= a.Length - 1
    invariant forall k :: j < k < a.Length ==> a[k] <= a[i]
    decreases j
  {
    j := j - 1;
  }

  a[i], a[j] := a[j], a[i];
  ReverseSubarray(a, i + 1, a.Length);
  return true;
}
