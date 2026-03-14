// Three Sum -- Test cases

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method {:axiom} ThreeSum(a: seq<int>, target: int) returns (found: bool, i: int, j: int, k: int)
  requires IsSorted(a)
  ensures found ==> 0 <= i < j < k < |a| && a[i] + a[j] + a[k] == target
  ensures !found ==> forall p, q, r :: 0 <= p < q < r < |a| ==> a[p] + a[q] + a[r] != target

method TestFound()
{
  var a := [-1, 0, 1, 2, -1, 4];
  // Not sorted, but let's use sorted input
  var b := [-1, -1, 0, 1, 2, 4];
  var f, i, j, k := ThreeSum(b, 0);
  if f { assert b[i] + b[j] + b[k] == 0; }
}

method TestNotFound()
{
  var a := [1, 2, 3];
  var f, i, j, k := ThreeSum(a, 100);
}

method TestTooSmall()
{
  var a := [1, 2];
  var f, i, j, k := ThreeSum(a, 3);
  assert !f;
}
