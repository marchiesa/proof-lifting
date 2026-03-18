// Sum of the integer sequence 1 + 2 + ... + n
ghost function TotalSum(n: int): int
  requires n >= 0
{
  n * (n + 1) / 2
}

ghost function Abs(x: int): int
{
  if x >= 0 then x else -x
}

// Sum of elements assigned to set A in a partition of {1..|assignment|}.
// assignment[i] == true means element (i+1) is in set A.
ghost function PartitionSumA(assignment: seq<bool>): int
  decreases |assignment|
{
  if |assignment| == 0 then 0
  else PartitionSumA(assignment[..|assignment|-1]) +
       (if assignment[|assignment|-1] then |assignment| else 0)
}

// |sum(A) - sum(B)| for a partition of {1..n}
ghost function PartitionDiff(assignment: seq<bool>, n: int): int
  requires n >= 0
  requires |assignment| == n
{
  Abs(2 * PartitionSumA(assignment) - TotalSum(n))
}

// Whether target is achievable as a subset sum of {1..n}.
// A subset of {1..n} sums to target iff either:
//   - target == 0 (empty subset), or
//   - n is included and target-n is achievable from {1..n-1}, or
//   - n is excluded and target is achievable from {1..n-1}.
ghost predicate IsSubsetSum(n: nat, target: int)
  decreases n
{
  if target < 0 then false
  else if target == 0 then true
  else if n == 0 then false
  else IsSubsetSum(n - 1, target - n) || IsSubsetSum(n - 1, target)
}

// d is the minimum possible |sum(A) - sum(B)| over all partitions of {1..n}.
//
// For any partition of {1..n} into sets A and B:
//   sum(A) + sum(B) = TotalSum(n)
//   |sum(A) - sum(B)| = |TotalSum(n) - 2 * sum(A)|
// So minimizing the difference is equivalent to finding a subset sum
// of {1..n} as close to TotalSum(n)/2 as possible.
// d is optimal when (TotalSum(n) - d)/2 is a valid subset sum and
// no smaller non-negative d satisfies this.
ghost predicate IsOptimalPartitionDiff(n: nat, d: int)
{
  var total := TotalSum(n);
  // d is non-negative
  d >= 0
  // Achievability: a partition with this exact difference exists
  && (total - d) % 2 == 0
  && IsSubsetSum(n, (total - d) / 2)
  // Optimality: no smaller non-negative difference is achievable
  && (forall d' | 0 <= d' < d ::
       (total - d') % 2 != 0 || !IsSubsetSum(n, (total - d') / 2))
}

method IntegerSequenceDividing(n: int) returns (result: int)
  requires n >= 0
  ensures IsOptimalPartitionDiff(n, result)
{
  var m := n % 4;
  if m == 0 || m == 3 {
    return 0;
  } else {
    return 1;
  }
}