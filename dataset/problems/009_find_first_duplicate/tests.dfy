// Find First Duplicate -- Test cases

predicate HasDuplicate(a: seq<int>, idx: int)
  requires 0 <= idx < |a|
{
  exists j :: 0 <= j < idx && a[j] == a[idx]
}

predicate AllDistinctBefore(a: seq<int>, idx: int)
  requires 0 <= idx <= |a|
{
  forall i :: 0 <= i < idx ==> (forall j :: 0 <= j < i ==> a[j] != a[i])
}

method {:axiom} FindFirstDuplicate(a: seq<int>) returns (index: int)
  ensures index == -1 ==> AllDistinctBefore(a, |a|)
  ensures 0 <= index < |a| ==> HasDuplicate(a, index) && AllDistinctBefore(a, index)
  ensures index < 0 ==> index == -1

method TestDuplicateExists()
{
  var a := [1, 2, 3, 2, 5];
  var idx := FindFirstDuplicate(a);
  // a[1] == 2 == a[3], so there's a duplicate
  // If idx == -1, then AllDistinctBefore(a, 5) holds, meaning all distinct
  // But a[1] == a[3] contradicts that
  if idx == -1 {
    assert AllDistinctBefore(a, |a|);
    // i=3, j=1: a[1] should != a[3], but both are 2
    assert a[1] != a[3];  // contradiction
  }
  assert idx != -1;
  assert idx >= 0;
}

method TestNoDuplicate()
{
  var a := [1, 2, 3, 4];
  var idx := FindFirstDuplicate(a);
  // All elements are distinct
  // If idx >= 0, then HasDuplicate(a, idx) holds
  if 0 <= idx < |a| {
    assert HasDuplicate(a, idx);
  }
}

method TestImmediateDuplicate()
{
  var a := [5, 5];
  var idx := FindFirstDuplicate(a);
  if idx == -1 {
    assert AllDistinctBefore(a, |a|);
    assert a[0] != a[1];  // contradiction: both are 5
  }
  assert idx != -1;
  assert idx >= 0;
}

method TestEmpty()
{
  var a: seq<int> := [];
  var idx := FindFirstDuplicate(a);
  assert !(0 <= idx < |a|);
}

method TestSingle()
{
  var a := [42];
  var idx := FindFirstDuplicate(a);
  // Only one element, so no duplicate is possible
  if 0 <= idx < |a| {
    assert HasDuplicate(a, idx);
    // idx must be 0 (only valid index), but HasDuplicate(a, 0) requires
    // exists j :: 0 <= j < 0 && ..., which is vacuously false
  }
}
