// Merge Two Sorted Arrays -- Test cases

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method {:axiom} MergeArrays(a: array<int>, b: array<int>) returns (c: array<int>)
  requires IsSorted(a[..])
  requires IsSorted(b[..])
  ensures IsSorted(c[..])
  ensures c.Length == a.Length + b.Length
  ensures multiset(c[..]) == multiset(a[..]) + multiset(b[..])

method TestMerge()
{
  var a := new int[] [1, 3, 5];
  var b := new int[] [2, 4, 6];
  var c := MergeArrays(a, b);
  assert c.Length == 6;
  assert IsSorted(c[..]);
}

method TestMergeWithEmpty()
{
  var a := new int[] [1, 2, 3];
  var b := new int[] [];
  var c := MergeArrays(a, b);
  assert c.Length == 3;
  assert IsSorted(c[..]);
}

method TestMergeBothEmpty()
{
  var a := new int[] [];
  var b := new int[] [];
  var c := MergeArrays(a, b);
  assert c.Length == 0;
}

method TestMergeDuplicates()
{
  var a := new int[] [1, 2, 2];
  var b := new int[] [2, 3, 3];
  var c := MergeArrays(a, b);
  assert c.Length == 6;
  assert IsSorted(c[..]);
}
