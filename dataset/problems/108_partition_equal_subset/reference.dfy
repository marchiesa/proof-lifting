// Partition Equal Subset Sum -- Reference solution with invariants

function SumSeq(a: seq<int>): int
{
  if |a| == 0 then 0 else a[0] + SumSeq(a[1..])
}

function CanPartition(a: seq<int>, n: int, target: int): bool
  requires 0 <= n <= |a|
  decreases n, if target >= 0 then target else 0
{
  if target == 0 then true
  else if target < 0 || n == 0 then false
  else CanPartition(a, n-1, target) || CanPartition(a, n-1, target - a[n-1])
}

lemma SumSeqNonNeg(a: seq<int>)
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures SumSeq(a) >= 0
  decreases |a|
{
  if |a| > 0 {
    SumSeqNonNeg(a[1..]);
  }
}

lemma SumSeqAppend(a: seq<int>, i: int)
  requires 0 <= i < |a|
  ensures SumSeq(a[..i+1]) == SumSeq(a[..i]) + a[i]
  decreases i
{
  if i == 0 {
    assert a[..1] == [a[0]];
    assert a[..0] == [];
  } else {
    assert a[..i+1][1..] == a[1..i+1];
    assert a[..i][1..] == a[1..i];
    SumSeqAppend(a[1..], i - 1);
    assert a[1..][..i] == a[1..i+1];
    assert a[1..][..i-1] == a[1..i];
  }
}

method PartitionEqualSubset(a: seq<int>) returns (result: bool)
  requires |a| > 0
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures result <==> (SumSeq(a) % 2 == 0 && CanPartition(a, |a|, SumSeq(a) / 2))
{
  var total := 0;
  var k := 0;
  while k < |a|
    invariant 0 <= k <= |a|
    invariant total == SumSeq(a[..k])
    decreases |a| - k
  {
    SumSeqAppend(a, k);
    total := total + a[k];
    k := k + 1;
  }
  assert a[..|a|] == a;
  SumSeqNonNeg(a);
  if total % 2 != 0 {
    result := false;
    return;
  }
  var target := total / 2;
  assert target >= 0;
  var dp := [true] + seq(target, j => false);
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |dp| == target + 1
    invariant forall j :: 0 <= j <= target ==> dp[j] == CanPartition(a, i, j)
    decreases |a| - i
  {
    // Process in reverse to avoid using same element twice
    ghost var oldDp := dp;
    var j := target;
    while j >= a[i] && j >= 0
      invariant -1 <= j <= target
      invariant |dp| == target + 1
      // For indices > j: dp[idx] == CanPartition(a, i+1, idx)
      invariant forall idx :: j < idx <= target ==> dp[idx] == CanPartition(a, i + 1, idx)
      // For indices <= j: dp[idx] still == CanPartition(a, i, idx)
      invariant forall idx :: 0 <= idx <= j ==> dp[idx] == CanPartition(a, i, idx)
      decreases j + 1
    {
      if dp[j - a[i]] {
        dp := dp[..j] + [true] + dp[j+1..];
      }
      // dp[j] is now CanPartition(a, i, j) || CanPartition(a, i, j - a[i])
      // == CanPartition(a, i+1, j)
      j := j - 1;
    }
    // For j < a[i]: CanPartition(a, i+1, j) == CanPartition(a, i, j) since
    // j - a[i] < 0, so can't include a[i]
    assert forall idx :: 0 <= idx <= target ==> dp[idx] == CanPartition(a, i + 1, idx);
    i := i + 1;
  }
  result := dp[target];
}
