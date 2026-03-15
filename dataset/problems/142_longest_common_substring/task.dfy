// Longest Common Substring
// Task: Add loop invariants so that Dafny can verify this program.
// Brute-force: check each pair (i, j) and count matching length.

method LongestCommonSubstring(a: seq<char>, b: seq<char>) returns (length: int)
  ensures length >= 0
  ensures length <= |a|
  ensures length <= |b|
{
  length := 0;
  var i := 0;
  while i < |a|
    // invariant
  {
    var j := 0;
    while j < |b|
      // invariant
    {
      var k := 0;
      while i + k < |a| && j + k < |b| && a[i + k] == b[j + k]
        // invariant
      {
        k := k + 1;
      }
      if k > length {
        length := k;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
