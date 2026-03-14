// Rabin-Karp Pattern Matching -- Reference solution with invariants

method RabinKarp(text: seq<int>, pattern: seq<int>, base: int, modulus: int) returns (positions: seq<int>)
  requires |pattern| > 0
  requires |pattern| <= |text|
  requires base > 0 && modulus > 1
  ensures forall k :: 0 <= k < |positions| ==> 0 <= positions[k] <= |text| - |pattern|
{
  positions := [];
  var m := |pattern|;
  var n := |text|;
  var patHash := 0;
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    decreases m - i
  {
    patHash := (patHash * base + pattern[i]) % modulus;
    i := i + 1;
  }
  var textHash := 0;
  i := 0;
  while i < m
    invariant 0 <= i <= m
    decreases m - i
  {
    textHash := (textHash * base + text[i]) % modulus;
    i := i + 1;
  }
  var highPow := 1;
  i := 0;
  while i < m - 1
    invariant 0 <= i <= m - 1
    decreases m - 1 - i
  {
    highPow := (highPow * base) % modulus;
    i := i + 1;
  }
  i := 0;
  while i <= n - m
    invariant 0 <= i <= n - m + 1
    invariant forall k :: 0 <= k < |positions| ==> 0 <= positions[k] <= n - m
    decreases n - m - i + 1
  {
    if textHash == patHash {
      var isMatch := true;
      var j := 0;
      while j < m
        invariant 0 <= j <= m
        invariant isMatch ==> forall k :: 0 <= k < j ==> text[i + k] == pattern[k]
        decreases m - j
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
