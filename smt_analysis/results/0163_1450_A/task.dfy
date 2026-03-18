// A string `sub` is a subsequence of `s` if `sub` can be obtained from `s`
// by deleting some (possibly zero or all) characters, preserving order.
ghost predicate IsSubsequence(sub: seq<char>, s: seq<char>)
  decreases |s|
{
  if |sub| == 0 then true
  else if |s| == 0 then false
  else if sub[|sub| - 1] == s[|s| - 1] then
    IsSubsequence(sub[..|sub| - 1], s[..|s| - 1])
  else
    IsSubsequence(sub, s[..|s| - 1])
}

// A string `b` is a permutation of `a` if they contain exactly the same
// characters with the same multiplicities.
ghost predicate IsPermutation(a: seq<char>, b: seq<char>)
{
  multiset(a) == multiset(b)
}

method AvoidTrygub(s: string) returns (b: string)
  ensures IsPermutation(s, b)
  ensures !IsSubsequence("trygub", b)
{
  var a := new char[|s|];
  var i := 0;
  while i < |s|
  {
    a[i] := s[i];
    i := i + 1;
  }

  // Insertion sort
  i := 1;
  while i < a.Length
  {
    var key := a[i];
    var j := i - 1;
    while j >= 0 && a[j] > key
    {
      a[j + 1] := a[j];
      j := j - 1;
    }
    a[j + 1] := key;
    i := i + 1;
  }

  b := a[..];
}