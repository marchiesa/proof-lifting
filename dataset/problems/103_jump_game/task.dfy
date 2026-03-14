// Jump Game: Can reach last index?
// Task: Add loop invariants so that Dafny can verify this program.

// MaxReach(a, n) = maximum index reachable using greedy from a[0..n]
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

method CanJump(a: seq<int>) returns (reachable: bool)
  requires |a| > 0
  requires forall k :: 0 <= k < |a| ==> a[k] >= 0
  ensures reachable <==> MaxReach(a, |a|) >= |a| - 1
{
  var maxReach := 0;
  var i := 0;
  while i < |a|
  {
    if i > maxReach {
      reachable := false;
      return;
    }
    if i + a[i] > maxReach {
      maxReach := i + a[i];
    }
    i := i + 1;
  }
  reachable := true;
}
