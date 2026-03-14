// Partition Equal Subset Sum -- Test cases
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

method {:axiom} PartitionEqualSubset(a: seq<int>) returns (result: bool)
  requires |a| > 0
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures result <==> (SumSeq(a) % 2 == 0 && CanPartition(a, |a|, SumSeq(a) / 2))

method TestBasic() {
  // [1, 5, 11, 5] -> sum=22, target=11, can partition: {11} and {1,5,5}
  var r := PartitionEqualSubset([1, 5, 11, 5]);
}

method TestOddSum() {
  // [1, 2, 3, 5] -> sum=11 (odd), cannot partition
  var r := PartitionEqualSubset([1, 2, 3, 5]);
  assert !r;
}

method TestSingle() {
  var r := PartitionEqualSubset([0]);
  assert r;
}
