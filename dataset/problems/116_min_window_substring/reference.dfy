// Minimum Window Containing All Characters -- Reference solution

predicate ContainsAll(window: seq<int>, t: seq<int>)
{
  forall i :: 0 <= i < |t| ==> multiset(window)[t[i]] >= multiset(t)[t[i]]
}

method MinWindowSubstring(s: seq<int>, t: seq<int>) returns (bestLen: int, bestStart: int)
  requires |t| > 0
  ensures bestLen == -1 || bestLen > 0
  ensures bestLen > 0 ==> 0 <= bestStart && bestStart + bestLen <= |s| && ContainsAll(s[bestStart..bestStart+bestLen], t)
{
  bestLen := -1;
  bestStart := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant bestLen == -1 || (bestLen > 0 && 0 <= bestStart && bestStart + bestLen <= |s| && ContainsAll(s[bestStart..bestStart+bestLen], t))
    decreases |s| - i
  {
    var j := i;
    while j <= |s|
      invariant i <= j <= |s| + 1
      invariant bestLen == -1 || (bestLen > 0 && 0 <= bestStart && bestStart + bestLen <= |s| && ContainsAll(s[bestStart..bestStart+bestLen], t))
      decreases |s| + 1 - j
    {
      if j <= |s| && ContainsAll(s[i..j], t) {
        if bestLen == -1 || j - i < bestLen {
          bestLen := j - i;
          if bestLen == 0 { bestLen := 1; } // ensure > 0
          bestStart := i;
        }
        break;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
