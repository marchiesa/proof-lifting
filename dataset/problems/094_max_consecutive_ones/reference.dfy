// Maximum Consecutive Ones -- Reference solution with invariants

function RunOfOnes(a: seq<int>, i: int): int
  requires 0 <= i <= |a|
  decreases i
{
  if i == 0 then 0
  else if a[i-1] == 1 then 1 + RunOfOnes(a, i-1)
  else 0
}

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

lemma RunOfOnesNonNeg(a: seq<int>, i: int)
  requires 0 <= i <= |a|
  ensures RunOfOnes(a, i) >= 0
  decreases i
{
  if i > 0 && a[i-1] == 1 {
    RunOfOnesNonNeg(a, i-1);
  }
}

lemma MaxRunNonNeg(a: seq<int>, i: int)
  requires 0 <= i <= |a|
  ensures MaxRun(a, i) >= 0
  decreases i
{
  if i > 0 {
    MaxRunNonNeg(a, i-1);
    RunOfOnesNonNeg(a, i);
  }
}

method MaxConsecutiveOnes(a: seq<int>) returns (maxCount: int)
  ensures maxCount == MaxRun(a, |a|)
{
  maxCount := 0;
  var current := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant current == RunOfOnes(a, i)
    invariant maxCount == MaxRun(a, i)
    decreases |a| - i
  {
    if a[i] == 1 {
      current := current + 1;
    } else {
      current := 0;
    }
    assert current == RunOfOnes(a, i + 1);
    if current > maxCount {
      maxCount := current;
    }
    assert maxCount == MaxRun(a, i + 1);
    i := i + 1;
  }
}
