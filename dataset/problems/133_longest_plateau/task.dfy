// Longest Plateau
// Task: Add loop invariants so that Dafny can verify this program.
// Find the length of the longest run of equal consecutive elements.

predicate PlateauAt(a: seq<int>, start: int, len: int)
  requires 0 <= start
  requires len >= 1
  requires start + len <= |a|
{
  forall i :: start <= i < start + len ==> a[i] == a[start]
}

predicate HasPlateau(a: seq<int>, len: int)
  requires |a| > 0
  requires len >= 1
{
  exists s :: 0 <= s && s + len <= |a| && PlateauAt(a, s, len)
}

method LongestPlateau(a: seq<int>) returns (maxLen: int)
  requires |a| > 0
  ensures 1 <= maxLen <= |a|
  ensures HasPlateau(a, maxLen)
  ensures forall s, l :: 0 <= s && l > maxLen && l <= |a| && s + l <= |a| ==> !PlateauAt(a, s, l)
{
  maxLen := 1;
  var curLen := 1;
  var i := 1;
  while i < |a|
  {
    if a[i] == a[i-1] {
      curLen := curLen + 1;
      if curLen > maxLen {
        maxLen := curLen;
      }
    } else {
      curLen := 1;
    }
    i := i + 1;
  }
}
