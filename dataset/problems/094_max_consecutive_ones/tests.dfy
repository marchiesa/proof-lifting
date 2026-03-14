// Maximum Consecutive Ones -- Test cases

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

method {:axiom} MaxConsecutiveOnes(a: seq<int>) returns (maxCount: int)
  ensures maxCount == MaxRun(a, |a|)

method TestBasic()
{
  var a := [1, 1, 0, 1, 1, 1];
  var m := MaxConsecutiveOnes(a);
  assert m == MaxRun(a, 6);
}

method TestAllOnes()
{
  var a := [1, 1, 1];
  var m := MaxConsecutiveOnes(a);
}

method TestNoOnes()
{
  var a := [0, 0, 0];
  var m := MaxConsecutiveOnes(a);
}

method TestEmpty()
{
  var a: seq<int> := [];
  var m := MaxConsecutiveOnes(a);
  assert m == 0;
}

method TestSingleOne()
{
  var a := [1];
  var m := MaxConsecutiveOnes(a);
}
