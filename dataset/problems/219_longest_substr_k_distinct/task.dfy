// Longest Substring with At Most K Distinct Characters
// Task: Add loop invariants so that Dafny can verify this program.

function DistinctCount(s: seq<int>, lo: int, hi: int): nat
  requires 0 <= lo <= hi <= |s|
{
  |set i | lo <= i < hi :: s[i]|
}

function Max(a: int, b: int): int { if a >= b then a else b }

method LongestKDistinct(s: seq<int>, k: int) returns (length: int)
  requires k >= 1
  ensures length >= 0
  ensures length <= |s|
{
  if |s| == 0 {
    return 0;
  }
  length := 0;
  var i := 0;
  while i < |s|
  {
    var j := i;
    var distinct: set<int> := {};
    while j < |s| && (s[j] in distinct || |distinct| < k)
    {
      distinct := distinct + {s[j]};
      j := j + 1;
    }
    length := Max(length, j - i);
    i := i + 1;
  }
}
