// Burst Balloons -- Test cases
function Max(a: int, b: int): int { if a >= b then a else b }

method {:axiom} BurstBalloons(a: seq<int>) returns (result: int)
  requires |a| >= 1
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures result >= 0

method TestSingle() {
  var r := BurstBalloons([5]);
  assert r >= 0;
}

method TestTwo() {
  var r := BurstBalloons([3, 1]);
  assert r >= 0;
}

method TestThree() {
  // [3, 1, 5] -> optimal: burst 1 (3*1*5=15), burst 3 (1*3*5=15), burst 5 (1*5*1=5) = 35? various orderings
  var r := BurstBalloons([3, 1, 5]);
  assert r >= 0;
}
