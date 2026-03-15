// Minimum Number of Refueling Stops
// Task: Add loop invariants so that Dafny can verify this program.

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
  // DP: dp[t] = max distance reachable with t stops
  var n := |positions|;
  var dp := [startFuel] + seq(n, _ => 0);

  var i := 0;
  while i < n
  {
    var t := i;
    while t >= 0
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
  {
    if dp[i] >= target {
      stops := i;
      return;
    }
    i := i + 1;
  }
}
