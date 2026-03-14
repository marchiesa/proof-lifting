// Word Break (DP)
// Task: Add loop invariants so that Dafny can verify this program.
// Check if a string (seq<int>) can be segmented into words from a dictionary.

predicate InDict(dict: seq<seq<int>>, word: seq<int>)
{
  exists i :: 0 <= i < |dict| && dict[i] == word
}

// Spec: can s[0..n] be broken into dictionary words?
function Breakable(s: seq<int>, dict: seq<seq<int>>, n: int): bool
  requires 0 <= n <= |s|
  decreases n
{
  if n == 0 then true
  else exists k :: 0 <= k < n && Breakable(s, dict, k) && InDict(dict, s[k..n])
}

method WordBreak(s: seq<int>, dict: seq<seq<int>>) returns (result: bool)
  ensures result == Breakable(s, dict, |s|)
{
  // dp[i] == Breakable(s, dict, i)
  var dp := [true] + seq(|s|, i => false);
  var i := 1;
  while i <= |s|
  {
    var j := 0;
    while j < i
    {
      if dp[j] {
        // Check if s[j..i] is in dictionary
        var word := s[j..i];
        var k := 0;
        var found := false;
        while k < |dict|
        {
          if dict[k] == word {
            found := true;
            break;
          }
          k := k + 1;
        }
        if found {
          dp := dp[..i] + [true] + dp[i+1..];
          break;
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := dp[|s|];
}
