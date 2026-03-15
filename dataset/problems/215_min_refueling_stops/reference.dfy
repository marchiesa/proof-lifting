// Minimum Refueling Stops -- Reference solution with invariants

function Max(a: int, b: int): int { if a >= b then a else b }

method MinRefuelStops(target: int, startFuel: int, positions: seq<int>, fuels: seq<int>) returns (stops: int)
  requires target > 0
  requires startFuel >= 0
  requires |positions| == |fuels|
  requires forall i :: 0 <= i < |positions| ==> 0 < positions[i] < target
  requires forall i :: 0 <= i < |fuels| ==> fuels[i] > 0
  requires forall i, j :: 0 <= i < j < |positions| ==> positions[i] < positions[j]
  ensures stops >= -1
{
  var n := |positions|;
  var dp := [startFuel] + seq(n, _ => 0);

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |dp| == n + 1
    invariant dp[0] >= 0
    decreases n - i
  {
    var t := i;
    while t >= 0
      invariant -1 <= t <= i
      invariant |dp| == n + 1
      decreases t + 1
    {
      if dp[t] >= positions[i] {
        dp := dp[..t+1] + [Max(dp[t+1], dp[t] + fuels[i])] + dp[t+2..];
      }
      t := t - 1;
    }
    i := i + 1;
  }

  stops := -1;
  i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant stops == -1
    invariant |dp| == n + 1
    decreases n + 1 - i
  {
    if dp[i] >= target {
      stops := i;
      return;
    }
    i := i + 1;
  }
}
