// Minimum Window Containing All Characters -- Test cases
predicate ContainsAll(window: seq<int>, t: seq<int>)
{
  forall i :: 0 <= i < |t| ==> multiset(window)[t[i]] >= multiset(t)[t[i]]
}

method {:axiom} MinWindowSubstring(s: seq<int>, t: seq<int>) returns (bestLen: int, bestStart: int)
  requires |t| > 0
  ensures bestLen == -1 || bestLen > 0
  ensures bestLen > 0 ==> 0 <= bestStart && bestStart + bestLen <= |s| && ContainsAll(s[bestStart..bestStart+bestLen], t)

method TestFound() {
  // s = [1,2,3,1,2], t = [1,2] -> window [1,2] at start 0
  var len, start := MinWindowSubstring([1, 2, 3, 1, 2], [1, 2]);
}

method TestNotFound() {
  // s = [1,2,3], t = [4]
  var len, start := MinWindowSubstring([1, 2, 3], [4]);
}

method TestExact() {
  // s = [1], t = [1]
  var len, start := MinWindowSubstring([1], [1]);
}
