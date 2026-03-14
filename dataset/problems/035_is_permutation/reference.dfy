// Check if Array is a Permutation of 0..n-1 -- Reference solution with invariants

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
    invariant 0 <= k <= n
    invariant forall j :: 0 <= j < k ==> !seen[j]
    decreases n - k
  {
    seen[k] := false;
    k := k + 1;
  }

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < n ==> (seen[j] <==> exists m :: 0 <= m < i && a[m] == j)
    invariant forall p :: 0 <= p < i ==> 0 <= a[p] < n
    invariant forall p, q :: 0 <= p < q < i ==> a[p] != a[q]
    decreases n - i
  {
    if a[i] < 0 || a[i] >= n || seen[a[i]] {
      if a[i] < 0 || a[i] >= n {
        assert !IsPermutation(a);
      } else {
        // seen[a[i]] is true, so there exists m < i with a[m] == a[i]
        assert exists m :: 0 <= m < i && a[m] == a[i];
        assert !IsPermutation(a);
      }
      return false;
    }
    seen[a[i]] := true;
    i := i + 1;
  }
  return true;
}
