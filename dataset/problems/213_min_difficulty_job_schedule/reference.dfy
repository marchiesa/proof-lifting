// Minimum Difficulty of Job Schedule -- Reference solution with invariants

function Max(a: int, b: int): int { if a >= b then a else b }
function Min(a: int, b: int): int { if a <= b then a else b }

method MinDifficulty(jobs: seq<int>, d: int) returns (result: int)
  requires d >= 1
  requires |jobs| >= d
  requires forall i :: 0 <= i < |jobs| ==> jobs[i] >= 1
  ensures result >= 0 || result == -1
{
  var n := |jobs|;
  if n < d {
    result := -1;
    return;
  }
  var INF := 999999999;
  var dp := seq(n * d, _ => INF);

  var maxSoFar := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |dp| == n * d
    invariant maxSoFar >= 0
    decreases n - i
  {
    maxSoFar := Max(maxSoFar, jobs[i]);
    dp := dp[..i * d] + [maxSoFar] + dp[i * d + 1..];
    i := i + 1;
  }

  var day := 1;
  while day < d
    invariant 1 <= day <= d
    invariant |dp| == n * d
    decreases d - day
  {
    i := day;
    while i < n
      invariant day <= i <= n
      invariant |dp| == n * d
      decreases n - i
    {
      var best := INF;
      var dayMax := 0;
      var j := i;
      while j >= day
        invariant day - 1 <= j <= i
        invariant dayMax >= 0
        invariant best >= 0
        invariant |dp| == n * d
        decreases j - day + 1
      {
        dayMax := Max(dayMax, jobs[j]);
        var prev := dp[(j - 1) * d + (day - 1)];
        if prev < INF {
          best := Min(best, prev + dayMax);
        }
        j := j - 1;
      }
      dp := dp[..i * d + day] + [best] + dp[i * d + day + 1..];
      i := i + 1;
    }
    day := day + 1;
  }
  result := dp[(n - 1) * d + (d - 1)];
  if result >= INF {
    result := -1;
  }
}
