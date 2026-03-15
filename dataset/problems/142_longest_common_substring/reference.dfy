// Longest Common Substring -- Reference solution with invariants
// Brute-force: check each pair (i, j) and count matching length

method LongestCommonSubstring(a: seq<char>, b: seq<char>) returns (length: int)
  ensures length >= 0
  ensures length <= |a|
  ensures length <= |b|
{
  length := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant length >= 0
    invariant length <= |a|
    invariant length <= |b|
    decreases |a| - i
  {
    var j := 0;
    while j < |b|
      invariant 0 <= j <= |b|
      invariant length >= 0
      invariant length <= |a|
      invariant length <= |b|
      decreases |b| - j
    {
      // Count how many chars match starting at a[i], b[j]
      var k := 0;
      while i + k < |a| && j + k < |b| && a[i + k] == b[j + k]
        invariant 0 <= k
        invariant i + k <= |a|
        invariant j + k <= |b|
        decreases |a| - i - k
      {
        k := k + 1;
      }
      if k > length {
        assert k <= |a| - i <= |a|;
        assert k <= |b| - j <= |b|;
        length := k;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
