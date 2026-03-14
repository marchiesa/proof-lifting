// Is Sorted Check -- Reference solution with invariants

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

lemma SortedFromAdjacent(a: seq<int>)
  requires forall i :: 0 <= i < |a| - 1 ==> a[i] <= a[i + 1]
  ensures IsSorted(a)
{
  if |a| <= 1 {
  } else {
    forall i, j | 0 <= i < j < |a|
      ensures a[i] <= a[j]
    {
      // Induction on j - i
      if j == i + 1 {
      } else {
        SortedFromAdjacentHelper(a, i, j);
      }
    }
  }
}

lemma SortedFromAdjacentHelper(a: seq<int>, i: int, j: int)
  requires forall k :: 0 <= k < |a| - 1 ==> a[k] <= a[k + 1]
  requires 0 <= i < j < |a|
  ensures a[i] <= a[j]
  decreases j - i
{
  if j == i + 1 {
  } else {
    SortedFromAdjacentHelper(a, i, j - 1);
  }
}

method IsSortedCheck(a: seq<int>) returns (sorted: bool, wit: int)
  ensures sorted <==> IsSorted(a)
  ensures !sorted ==> 0 <= wit < |a| - 1 && a[wit] > a[wit + 1]
{
  if |a| <= 1 {
    return true, 0;
  }
  var i := 0;
  while i < |a| - 1
    invariant 0 <= i <= |a| - 1
    invariant forall k :: 0 <= k < i ==> a[k] <= a[k + 1]
    decreases |a| - 1 - i
  {
    if a[i] > a[i + 1] {
      return false, i;
    }
    i := i + 1;
  }
  SortedFromAdjacent(a);
  return true, 0;
}
