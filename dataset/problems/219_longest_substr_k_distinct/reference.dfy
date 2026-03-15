// Longest Substring with At Most K Distinct -- Reference solution

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
    invariant 0 <= i <= |s|
    invariant 0 <= length <= |s|
    decreases |s| - i
  {
    var j := i;
    var distinct: set<int> := {};
    while j < |s| && (s[j] in distinct || |distinct| < k)
      invariant i <= j <= |s|
      invariant |distinct| <= k
      invariant forall x :: x in distinct ==> exists m :: i <= m < j && s[m] == x
      decreases |s| - j
    {
      distinct := distinct + {s[j]};
      j := j + 1;
    }
    length := Max(length, j - i);
    i := i + 1;
  }
}
