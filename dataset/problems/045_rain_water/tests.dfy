// Rain Water Trapping -- Test cases

method {:axiom} TrapWater(h: seq<int>) returns (water: int)
  requires |h| > 0
  requires forall i :: 0 <= i < |h| ==> h[i] >= 0
  ensures water >= 0

method TestClassic()
{
  var w := TrapWater([0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1]);
  assert w >= 0;
}

method TestFlat()
{
  var w := TrapWater([3, 3, 3, 3]);
  assert w >= 0;
}

method TestIncreasing()
{
  var w := TrapWater([1, 2, 3, 4]);
  assert w >= 0;
}

method TestSingle()
{
  var w := TrapWater([5]);
  assert w >= 0;
}
