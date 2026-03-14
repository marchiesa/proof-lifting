// Jump Game -- Test cases

function MaxReach(a: seq<int>, n: int): int
  requires forall k :: 0 <= k < |a| ==> a[k] >= 0
  requires 0 <= n <= |a|
{
  if n == 0 then 0
  else
    var prev := MaxReach(a, n - 1);
    if n - 1 <= prev then
      if n - 1 + a[n-1] > prev then n - 1 + a[n-1] else prev
    else prev
}

method {:axiom} CanJump(a: seq<int>) returns (reachable: bool)
  requires |a| > 0
  requires forall k :: 0 <= k < |a| ==> a[k] >= 0
  ensures reachable <==> MaxReach(a, |a|) >= |a| - 1

method TestReachable()
{
  var a := [2, 3, 1, 1, 4];
  var r := CanJump(a);
}

method TestUnreachable()
{
  var a := [3, 2, 1, 0, 4];
  var r := CanJump(a);
}

method TestSingle()
{
  var a := [0];
  var r := CanJump(a);
  assert MaxReach(a, 1) >= 0;
  assert r;
}
