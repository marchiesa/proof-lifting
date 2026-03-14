// Check if Array is a Permutation of 0..n-1
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsPermutation(a: seq<int>)
{
  (forall i :: 0 <= i < |a| ==> 0 <= a[i] < |a|) &&
  (forall i, j :: 0 <= i < j < |a| ==> a[i] != a[j])
}

method CheckPermutation(a: seq<int>) returns (result: bool)
  ensures result == IsPermutation(a)
{
  var n := |a|;
  var seen := new bool[n];
  var k := 0;
  while k < n
  {
    seen[k] := false;
    k := k + 1;
  }

  var i := 0;
  while i < n
  {
    if a[i] < 0 || a[i] >= n || seen[a[i]] {
      return false;
    }
    seen[a[i]] := true;
    i := i + 1;
  }
  return true;
}
