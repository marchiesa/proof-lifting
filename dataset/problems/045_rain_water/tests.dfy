// Rain Water Trapping -- Runtime spec tests

function Max(a: int, b: int): int { if a >= b then a else b }
function Min(a: int, b: int): int { if a <= b then a else b }

function MaxLeft(h: seq<int>, i: int): int
  requires 0 <= i < |h|
{
  if i == 0 then h[0]
  else Max(h[i], MaxLeft(h, i - 1))
}

function MaxRight(h: seq<int>, i: int): int
  requires 0 <= i < |h|
  decreases |h| - i
{
  if i == |h| - 1 then h[i]
  else Max(h[i], MaxRight(h, i + 1))
}

function WaterAt(h: seq<int>, i: int): int
  requires 0 <= i < |h|
{
  var level := Min(MaxLeft(h, i), MaxRight(h, i));
  if level > h[i] then level - h[i] else 0
}

function TotalWaterHelper(h: seq<int>, i: int): int
  requires 0 <= i <= |h|
  decreases |h| - i
{
  if i == |h| then 0
  else WaterAt(h, i) + TotalWaterHelper(h, i + 1)
}

function TotalWater(h: seq<int>): int
{
  if |h| == 0 then 0
  else TotalWaterHelper(h, 0)
}

method Main() {
  // Max/Min helper tests
  expect Max(3, 5) == 5, "max(3,5)=5";
  expect Max(5, 3) == 5, "max(5,3)=5";
  expect Min(3, 5) == 3, "min(3,5)=3";

  // MaxLeft tests
  var h := [0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1];
  expect MaxLeft(h, 0) == 0, "max left at 0";
  expect MaxLeft(h, 1) == 1, "max left at 1";
  expect MaxLeft(h, 3) == 2, "max left at 3";
  expect MaxLeft(h, 7) == 3, "max left at 7";

  // MaxRight tests
  expect MaxRight(h, 11) == 1, "max right at 11";
  expect MaxRight(h, 7) == 3, "max right at 7";

  // WaterAt tests
  expect WaterAt(h, 0) == 0, "no water at position 0";
  expect WaterAt(h, 2) == 1, "water at position 2 (between 1 and 2)";

  // TotalWater on classic example
  expect TotalWater(h) == 6, "classic example total water = 6";

  // Edge cases
  expect TotalWater([]) == 0, "no water on empty";
  expect TotalWater([5]) == 0, "no water on single bar";
  expect TotalWater([1, 2, 3, 4]) == 0, "no water on increasing";
  expect TotalWater([3, 3, 3]) == 0, "no water on flat";

  // Wrong answer
  expect TotalWater(h) != 5, "total water is not 5";

  print "All spec tests passed\n";
}
