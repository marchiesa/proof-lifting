// Next Permutation (Lexicographic)
// Task: Add loop invariants so that Dafny can verify this program.
// Finds the next lexicographically greater permutation.
// Returns true if successful, false if already the last permutation.

predicate IsSortedDesc(a: array<int>, lo: int, hi: int)
  reads a
  requires 0 <= lo <= hi <= a.Length
{
  forall i, j :: lo <= i < j < hi ==> a[i] >= a[j]
}

method ReverseSubarray(a: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= a.Length
  modifies a
  ensures forall k :: lo <= k < hi ==> a[k] == old(a[hi - 1 - (k - lo)])
  ensures forall k :: 0 <= k < lo ==> a[k] == old(a[k])
  ensures forall k :: hi <= k < a.Length ==> a[k] == old(a[k])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var i := lo;
  var j := hi - 1;
  while i < j
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

  // Find largest i such that a[i] < a[i+1]
  var i := a.Length - 2;
  while i >= 0 && a[i] >= a[i + 1]
  {
    i := i - 1;
  }

  if i < 0 {
    ReverseSubarray(a, 0, a.Length);
    return false;
  }

  // Find largest j such that a[j] > a[i]
  var j := a.Length - 1;
  while a[j] <= a[i]
  {
    j := j - 1;
  }

  a[i], a[j] := a[j], a[i];
  ReverseSubarray(a, i + 1, a.Length);
  return true;
}
