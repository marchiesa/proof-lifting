// Validate BST Property on Array -- Reference solution with invariants

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] < a[j]
}

lemma SortedFromAdjacent(a: seq<int>, n: int)
  requires 0 < n <= |a|
  requires forall i :: 0 <= i < n - 1 ==> a[i] < a[i+1]
  ensures forall i, j :: 0 <= i < j < n ==> a[i] < a[j]
  decreases n
{
  if n <= 1 {
  } else {
    SortedFromAdjacent(a, n - 1);
    forall i, j | 0 <= i < j < n
      ensures a[i] < a[j]
    {
      if j < n - 1 {
      } else {
        if i == j - 1 {
        } else {
          assert a[i] < a[j-1];
          assert a[j-1] < a[j];
        }
      }
    }
  }
}

method ValidateBST(a: seq<int>) returns (valid: bool)
  ensures valid <==> IsSorted(a)
{
  if |a| <= 1 {
    return true;
  }
  var i := 0;
  while i < |a| - 1
    invariant 0 <= i <= |a| - 1
    invariant forall k :: 0 <= k < i ==> a[k] < a[k+1]
    decreases |a| - 1 - i
  {
    if a[i] >= a[i + 1] {
      return false;
    }
    i := i + 1;
  }
  SortedFromAdjacent(a, |a|);
  return true;
}
