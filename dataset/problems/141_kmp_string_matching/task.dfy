// KMP String Matching
// Task: Add loop invariants so that Dafny can verify this program.
// Find first occurrence of pattern in text using KMP algorithm.

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
  // Simple brute force search (KMP-style but simplified)
  var i := 0;
  while i + |pattern| <= |text|
  {
    var j := 0;
    while j < |pattern| && text[i + j] == pattern[j]
    {
      j := j + 1;
    }
    if j == |pattern| {
      return i;
    }
    i := i + 1;
  }
  return -1;
}
