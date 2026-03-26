// Source: jaraco/jaraco.text/Stripper.common_prefix
// URL: https://github.com/jaraco/jaraco.text/blob/0fe070e9241cb1fdb737516a3f57da94a2618376/jaraco/text.py#L368-L375
// Original: Return the common prefix of two lines
// Gist: index = min(len(s1),len(s2)); while s1[:index] != s2[:index]: index -= 1

predicate IsCommonPrefix(prefix: seq<int>, s1: seq<int>, s2: seq<int>)
{
  |prefix| <= |s1| && |prefix| <= |s2| &&
  prefix == s1[..|prefix|] && prefix == s2[..|prefix|]
}

predicate IsMaximalCommonPrefix(prefix: seq<int>, s1: seq<int>, s2: seq<int>)
{
  IsCommonPrefix(prefix, s1, s2) &&
  (|prefix| == |s1| || |prefix| == |s2| || s1[|prefix|] != s2[|prefix|])
}

method CommonPrefix(s1: seq<int>, s2: seq<int>) returns (prefix: seq<int>)
  ensures IsMaximalCommonPrefix(prefix, s1, s2)
{
  var i := 0;
  var minLen := if |s1| < |s2| then |s1| else |s2|;
  while i < minLen && s1[i] == s2[i]
    invariant 0 <= i <= minLen
    invariant IsCommonPrefix(s1[..i], s1, s2)
  {
    assert s1[..i+1] == s1[..i] + [s1[i]];
    assert s2[..i+1] == s2[..i] + [s2[i]];
    i := i + 1;
  }
  prefix := s1[..i];
}
