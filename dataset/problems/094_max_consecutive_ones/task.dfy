// Maximum Consecutive Ones
// Task: Add loop invariants so that Dafny can verify this program.

// Length of run of 1s ending at position i (exclusive)
function RunOfOnes(a: seq<int>, i: int): int
  requires 0 <= i <= |a|
  decreases i
{
  if i == 0 then 0
  else if a[i-1] == 1 then 1 + RunOfOnes(a, i-1)
  else 0
}

// Maximum run of 1s in a[0..i]
function MaxRun(a: seq<int>, i: int): int
  requires 0 <= i <= |a|
  decreases i
{
  if i == 0 then 0
  else
    var cur := RunOfOnes(a, i);
    var prev := MaxRun(a, i-1);
    if cur > prev then cur else prev
}

method MaxConsecutiveOnes(a: seq<int>) returns (maxCount: int)
  ensures maxCount == MaxRun(a, |a|)
{
  maxCount := 0;
  var current := 0;
  var i := 0;
  while i < |a|
  {
    if a[i] == 1 {
      current := current + 1;
    } else {
      current := 0;
    }
    if current > maxCount {
      maxCount := current;
    }
    i := i + 1;
  }
}
