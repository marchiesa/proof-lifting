// Is Sorted Check
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
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
  {
    if a[i] > a[i + 1] {
      return false, i;
    }
    i := i + 1;
  }
  return true, 0;
}
