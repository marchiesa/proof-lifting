// KMP String Matching -- Reference solution with invariants

predicate IsMatch(text: seq<char>, pattern: seq<char>, pos: int)
  requires 0 <= pos
  requires pos + |pattern| <= |text|
{
  forall i :: 0 <= i < |pattern| ==> text[pos + i] == pattern[i]
}

predicate ContainsAt(text: seq<char>, pattern: seq<char>, pos: int)
{
  0 <= pos && pos + |pattern| <= |text| && IsMatch(text, pattern, pos)
}

method KMPSearch(text: seq<char>, pattern: seq<char>) returns (pos: int)
  requires |pattern| > 0
  ensures pos == -1 ==> forall k :: 0 <= k && k + |pattern| <= |text| ==> !IsMatch(text, pattern, k)
  ensures pos >= 0 ==> ContainsAt(text, pattern, pos)
  ensures pos >= 0 ==> forall k :: 0 <= k < pos && k + |pattern| <= |text| ==> !IsMatch(text, pattern, k)
{
  if |pattern| > |text| {
    return -1;
  }
  var i := 0;
  while i + |pattern| <= |text|
    invariant 0 <= i
    invariant forall k :: 0 <= k < i && k + |pattern| <= |text| ==> !IsMatch(text, pattern, k)
    decreases |text| - i
  {
    var j := 0;
    while j < |pattern| && text[i + j] == pattern[j]
      invariant 0 <= j <= |pattern|
      invariant i + |pattern| <= |text|
      invariant forall k :: 0 <= k < j ==> text[i + k] == pattern[k]
      decreases |pattern| - j
    {
      j := j + 1;
    }
    if j == |pattern| {
      assert IsMatch(text, pattern, i);
      return i;
    }
    assert j < |pattern| && text[i + j] != pattern[j];
    assert !IsMatch(text, pattern, i);
    i := i + 1;
  }
  return -1;
}
