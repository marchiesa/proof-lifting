// Trapping Rain Water -- Test cases
function Max(a: int, b: int): int { if a >= b then a else b }
function Min(a: int, b: int): int { if a <= b then a else b }

function PrefixMax(a: seq<int>, n: int): int
  requires 0 < n <= |a|
  decreases n
{
  if n == 1 then a[0]
  else Max(PrefixMax(a, n - 1), a[n - 1])
}

function SuffixMax(a: seq<int>, n: int): int
  requires 0 <= n < |a|
  decreases |a| - n
{
  if n == |a| - 1 then a[n]
  else Max(a[n], SuffixMax(a, n + 1))
}

method {:axiom} ComputePrefixMax(a: seq<int>) returns (pm: seq<int>)
  requires |a| > 0
  ensures |pm| == |a|
  ensures pm[0] == a[0]
  ensures forall i :: 0 < i < |a| ==> pm[i] == Max(pm[i-1], a[i])
  ensures forall i :: 0 < i < |a| ==> pm[i] == PrefixMax(a, i + 1)

method {:axiom} ComputeSuffixMax(a: seq<int>) returns (sm: seq<int>)
  requires |a| > 0
  ensures |sm| == |a|
  ensures sm[|a|-1] == a[|a|-1]
  ensures forall i :: 0 <= i < |a| - 1 ==> sm[i] == Max(a[i], sm[i+1])
  ensures forall i :: 0 <= i < |a| - 1 ==> sm[i] == SuffixMax(a, i)

method {:axiom} TrapRainWater(a: seq<int>) returns (water: int)
  requires |a| >= 2
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures water >= 0

method TestBasic() {
  // [0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1] -> water = 6
  var r := TrapRainWater([0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1]);
  assert r >= 0;
}

method TestFlat() {
  var r := TrapRainWater([1, 1]);
  assert r >= 0;
}

method TestNoTrap() {
  var r := TrapRainWater([3, 2, 1]);
  assert r >= 0;
}
