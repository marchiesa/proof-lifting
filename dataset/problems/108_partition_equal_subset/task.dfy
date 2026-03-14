// Partition Equal Subset Sum (DP)
// Task: Add loop invariants so that Dafny can verify this program.

function SumSeq(a: seq<int>): int
{
  if |a| == 0 then 0 else a[0] + SumSeq(a[1..])
}

// Can we select a subset of a[0..n] that sums to target?
function CanPartition(a: seq<int>, n: int, target: int): bool
  requires 0 <= n <= |a|
  decreases n, if target >= 0 then target else 0
{
  if target == 0 then true
  else if target < 0 || n == 0 then false
  else CanPartition(a, n-1, target) || CanPartition(a, n-1, target - a[n-1])
}

method PartitionEqualSubset(a: seq<int>) returns (result: bool)
  requires |a| > 0
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures result <==> (SumSeq(a) % 2 == 0 && CanPartition(a, |a|, SumSeq(a) / 2))
{
  // Compute total sum
  var total := 0;
  var k := 0;
  while k < |a|
  {
    total := total + a[k];
    k := k + 1;
  }
  if total % 2 != 0 {
    result := false;
    return;
  }
  var target := total / 2;
  // dp[j] = can we make sum j using elements seen so far
  var dp := [true] + seq(target, j => false);
  var i := 0;
  while i < |a|
  {
    var j := target;
    while j >= a[i] && j >= 0
    {
      if dp[j - a[i]] {
        dp := dp[..j] + [true] + dp[j+1..];
      }
      j := j - 1;
    }
    i := i + 1;
  }
  result := dp[target];
}
