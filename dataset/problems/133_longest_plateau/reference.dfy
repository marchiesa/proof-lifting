// Longest Plateau -- Reference solution with invariants

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
  ghost var maxStart := 0;
  ghost var curStart := 0;
  var i := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant 1 <= curLen <= i
    invariant 1 <= maxLen <= i
    invariant 0 <= curStart && curStart + curLen == i
    invariant PlateauAt(a, curStart, curLen)
    invariant curStart > 0 ==> a[curStart] != a[curStart - 1]
    invariant 0 <= maxStart && maxStart + maxLen <= i
    invariant PlateauAt(a, maxStart, maxLen)
    invariant curLen <= maxLen
    invariant forall s, l :: 0 <= s && l > maxLen && l <= i && s + l <= i ==> !PlateauAt(a, s, l)
    decreases |a| - i
  {
    if a[i] == a[i-1] {
      curLen := curLen + 1;
      if curLen > maxLen {
        maxLen := curLen;
        maxStart := curStart;
      }
    } else {
      curLen := 1;
      curStart := i;
    }
    i := i + 1;
  }
}
