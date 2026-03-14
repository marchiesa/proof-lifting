// Rabin-Karp Pattern Matching
// Task: Add loop invariants so that Dafny can verify this program.

method RabinKarp(text: seq<int>, pattern: seq<int>, base: int, modulus: int) returns (positions: seq<int>)
  requires |pattern| > 0
  requires |pattern| <= |text|
  requires base > 0 && modulus > 1
  ensures forall k :: 0 <= k < |positions| ==> 0 <= positions[k] <= |text| - |pattern|
{
  positions := [];
  var m := |pattern|;
  var n := |text|;
  // Compute pattern hash
  var patHash := 0;
  var i := 0;
  while i < m
  {
    patHash := (patHash * base + pattern[i]) % modulus;
    i := i + 1;
  }
  // Compute initial text window hash
  var textHash := 0;
  i := 0;
  while i < m
  {
    textHash := (textHash * base + text[i]) % modulus;
    i := i + 1;
  }
  // Compute base^(m-1) mod modulus
  var highPow := 1;
  i := 0;
  while i < m - 1
  {
    highPow := (highPow * base) % modulus;
    i := i + 1;
  }
  // Slide window
  i := 0;
  while i <= n - m
  {
    if textHash == patHash {
      // Verify match
      var isMatch := true;
      var j := 0;
      while j < m
      {
        if text[i + j] != pattern[j] {
          isMatch := false;
          break;
        }
        j := j + 1;
      }
      if isMatch {
        positions := positions + [i];
      }
    }
    if i < n - m {
      textHash := ((textHash - text[i] * highPow) * base + text[i + m]) % modulus;
    }
    i := i + 1;
  }
}
