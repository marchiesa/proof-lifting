// Jump Game -- Reference solution with invariants

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

lemma MaxReachStaysBlocked(a: seq<int>, n: int, m: int)
  requires forall k :: 0 <= k < |a| ==> a[k] >= 0
  requires 0 < n <= m <= |a|
  requires n - 1 > MaxReach(a, n - 1)
  ensures MaxReach(a, m) == MaxReach(a, n - 1)
  decreases m - n
{
  if m > n {
    assert MaxReach(a, n) == MaxReach(a, n - 1);
    assert n > MaxReach(a, n);
    MaxReachStaysBlocked(a, n + 1, m);
  }
}

method CanJump(a: seq<int>) returns (reachable: bool)
  requires |a| > 0
  requires forall k :: 0 <= k < |a| ==> a[k] >= 0
  ensures reachable <==> MaxReach(a, |a|) >= |a| - 1
{
  var maxReach := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant maxReach == MaxReach(a, i)
    invariant i <= maxReach + 1
    decreases |a| - i
  {
    if i > maxReach {
      // Blocked: i > MaxReach(a, i)
      MaxReachStaysBlocked(a, i + 1, |a|);
      assert MaxReach(a, |a|) == MaxReach(a, i);
      assert MaxReach(a, |a|) < i;
      assert i < |a|;
      reachable := false;
      return;
    }
    if i + a[i] > maxReach {
      maxReach := i + a[i];
    }
    i := i + 1;
  }
  // Loop completed: i == |a|, maxReach >= i - 1 = |a| - 1
  assert maxReach >= |a| - 1;
  reachable := true;
}
