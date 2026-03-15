// Maximum Profit Job Scheduling (DP)
// Task: Add loop invariants so that Dafny can verify this program.

// Given n jobs with start times, end times, and profits,
// find max profit from non-overlapping jobs.
// Jobs are given as three parallel sequences: startTimes, endTimes, profits.

function Max(a: int, b: int): int { if a >= b then a else b }

method MaxProfitJobScheduling(
  startTimes: seq<int>, endTimes: seq<int>, profits: seq<int>
) returns (result: int)
  requires |startTimes| == |endTimes| == |profits| > 0
  requires forall i :: 0 <= i < |profits| ==> profits[i] >= 0
  requires forall i :: 0 <= i < |startTimes| ==> startTimes[i] < endTimes[i]
  ensures result >= 0
{
  var n := |startTimes|;

  // Sort jobs by end time using selection sort
  var ends := new int[n];
  var starts := new int[n];
  var profs := new int[n];
  var i := 0;
  while i < n
  {
    ends[i] := endTimes[i];
    starts[i] := startTimes[i];
    profs[i] := profits[i];
    i := i + 1;
  }

  i := 0;
  while i < n
  {
    var best := i;
    var j := i + 1;
    while j < n
    {
      if ends[j] < ends[best] { best := j; }
      j := j + 1;
    }
    if best != i {
      var te := ends[i]; ends[i] := ends[best]; ends[best] := te;
      var ts := starts[i]; starts[i] := starts[best]; starts[best] := ts;
      var tp := profs[i]; profs[i] := profs[best]; profs[best] := tp;
    }
    i := i + 1;
  }

  // dp[i] = max profit considering first i jobs
  var dp := new int[n + 1];
  dp[0] := 0;

  i := 1;
  while i <= n
  {
    // Find latest job that doesn't overlap
    var latest := -1;
    var k := i - 2;
    while k >= 0
    {
      if ends[k] <= starts[i-1] {
        latest := k;
        break;
      }
      k := k - 1;
    }
    var includeProfit := profs[i-1] + (if latest >= 0 then dp[latest + 1] else 0);
    dp[i] := Max(dp[i-1], includeProfit);
    i := i + 1;
  }

  result := dp[n];
}
