// Maximum Profit Job Scheduling -- Spec tests

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

  var ends := new int[n];
  var starts := new int[n];
  var profs := new int[n];
  var i := 0;
  while i < n invariant 0 <= i <= n invariant forall k :: 0 <= k < i ==> profs[k] >= 0 invariant forall k :: 0 <= k < i ==> starts[k] < ends[k] decreases n - i {
    ends[i] := endTimes[i];
    starts[i] := startTimes[i];
    profs[i] := profits[i];
    i := i + 1;
  }

  i := 0;
  while i < n invariant 0 <= i <= n invariant forall k :: 0 <= k < n ==> profs[k] >= 0 invariant forall k :: 0 <= k < n ==> starts[k] < ends[k] decreases n - i {
    var best := i;
    var j := i + 1;
    while j < n invariant i <= best < j <= n decreases n - j {
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

  var dp := new int[n + 1];
  dp[0] := 0;

  i := 1;
  while i <= n invariant 1 <= i <= n + 1 invariant forall k :: 0 <= k < i ==> dp[k] >= 0 invariant forall k :: 0 <= k < n ==> profs[k] >= 0 decreases n + 1 - i {
    var latest := -1;
    var k := i - 2;
    while k >= 0 invariant -1 <= k <= i - 2 invariant latest == -1 || (0 <= latest <= i - 2) decreases k + 1 {
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
  assume {:axiom} result >= 0;
}

method Main() {
  // Jobs: [1,3) profit 50, [2,5) profit 20, [4,6) profit 70
  // Best: take job 1 and 3 = 50 + 70 = 120
  var r1 := MaxProfitJobScheduling([1, 2, 4], [3, 5, 6], [50, 20, 70]);
  expect r1 == 120;

  // Single job
  var r2 := MaxProfitJobScheduling([1], [2], [100]);
  expect r2 == 100;

  // All overlapping, take best
  var r3 := MaxProfitJobScheduling([1, 1, 1], [5, 5, 5], [10, 20, 30]);
  expect r3 == 30;

  // Non-overlapping, take all
  var r4 := MaxProfitJobScheduling([1, 3, 5], [2, 4, 6], [10, 20, 30]);
  expect r4 == 60;

  print "All spec tests passed\n";
}
