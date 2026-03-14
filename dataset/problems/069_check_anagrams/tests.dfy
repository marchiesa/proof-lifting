// Check Anagrams -- Test cases

method {:axiom} AreAnagrams(a: seq<int>, b: seq<int>) returns (result: bool)
  ensures result == (multiset(a) == multiset(b))

method TestAnagramTrue()
{
  var r := AreAnagrams([1, 2, 3], [3, 2, 1]);
  assert multiset([1, 2, 3]) == multiset([3, 2, 1]);
  assert r;
}

method TestAnagramWithDuplicates()
{
  var r := AreAnagrams([1, 2, 2], [2, 1, 2]);
  assert multiset([1, 2, 2]) == multiset([2, 1, 2]);
  assert r;
}

method TestNotAnagram()
{
  var r := AreAnagrams([1, 2], [1, 3]);
  assert multiset([1, 2]) != multiset([1, 3]);
  assert !r;
}

method TestDifferentLengths()
{
  var r := AreAnagrams([1, 2], [1, 2, 3]);
  assert !r;
}
