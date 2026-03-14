// Next Permutation -- Test cases

method {:axiom} NextPermutation(a: array<int>) returns (found: bool)
  modifies a
  ensures multiset(a[..]) == old(multiset(a[..]))

method TestBasic()
{
  var a := new int[] [1, 2, 3];
  var old_ms := multiset(a[..]);
  var found := NextPermutation(a);
  assert multiset(a[..]) == old_ms;
}

method TestDescending()
{
  var a := new int[] [3, 2, 1];
  var old_ms := multiset(a[..]);
  var found := NextPermutation(a);
  assert multiset(a[..]) == old_ms;
}

method TestSingle()
{
  var a := new int[] [1];
  var found := NextPermutation(a);
  assert multiset(a[..]) == multiset{1};
}

method TestDuplicates()
{
  var a := new int[] [1, 1, 2];
  var old_ms := multiset(a[..]);
  var found := NextPermutation(a);
  assert multiset(a[..]) == old_ms;
}
