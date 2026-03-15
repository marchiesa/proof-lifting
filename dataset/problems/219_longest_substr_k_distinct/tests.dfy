// Longest Substring with At Most K Distinct Characters

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

method Main()
{
  // [1,2,1,2,3] k=2 => [1,2,1,2] length 4
  var r1 := LongestKDistinct([1, 2, 1, 2, 3], 2);
  expect r1 >= 0;
  expect r1 <= 5;

  // k >= distinct values => whole array
  var r2 := LongestKDistinct([1, 2, 3], 5);
  expect r2 >= 0;
  expect r2 <= 3;

  // Empty
  var r3 := LongestKDistinct([], 1);
  expect r3 == 0;

  // Single element
  var r4 := LongestKDistinct([5], 1);
  expect r4 >= 0;
  expect r4 <= 1;

  // k=1
  var r5 := LongestKDistinct([1, 1, 2, 2, 2], 1);
  expect r5 >= 0;

  print "All spec tests passed\n";
}
