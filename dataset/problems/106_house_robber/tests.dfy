// House Robber -- Test cases
function Max(a: int, b: int): int { if a >= b then a else b }

function Rob(a: seq<int>, n: int): int
  requires 0 <= n <= |a|
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  decreases n
{
  if n == 0 then 0
  else if n == 1 then a[0]
  else Max(Rob(a, n - 1), Rob(a, n - 2) + a[n - 1])
}

method {:axiom} HouseRobber(a: seq<int>) returns (result: int)
  requires |a| > 0
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures result == Rob(a, |a|)

method TestBasic() { var r := HouseRobber([1, 2, 3, 1]); }
method TestSingle() { var r := HouseRobber([5]); assert r == 5; }
