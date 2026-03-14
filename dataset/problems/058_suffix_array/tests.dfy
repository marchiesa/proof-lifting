// Suffix Array Construction -- Test cases

predicate IsPermutation(sa: seq<int>, n: int)
{
  |sa| == n &&
  (forall i :: 0 <= i < n ==> 0 <= sa[i] < n) &&
  (forall i, j :: 0 <= i < j < n ==> sa[i] != sa[j])
}

method {:axiom} SuffixArray(s: seq<int>) returns (sa: seq<int>)
  requires |s| > 0
  ensures |sa| == |s|
  ensures IsPermutation(sa, |s|)

method TestSingle()
{
  var sa := SuffixArray([42]);
  assert |sa| == 1;
  assert sa[0] == 0;
}

method TestTwo()
{
  var sa := SuffixArray([1, 2]);
  assert |sa| == 2;
  assert sa[0] != sa[1];
  assert 0 <= sa[0] < 2;
  assert 0 <= sa[1] < 2;
}

method TestRepeated()
{
  var sa := SuffixArray([1, 1, 1]);
  assert |sa| == 3;
  assert IsPermutation(sa, 3);
}
