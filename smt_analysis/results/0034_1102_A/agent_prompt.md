Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Integer Sequence Dividing
You are given an integer sequence $$$1, 2, \dots, n$$$. You have to divide it into two sets $$$A$$$ and $$$B$$$ in such a way that each element belongs to exactly one set and $$$|sum(A) - sum(B)|$$$ is minimum possible.

The value $$$|x|$$$ is the absolute value of $$$x$$$ and $$$sum(S)$$$ is the sum of elements of the set $$$S$$$.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0034_1102_A/task.dfy

```dafny
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
```

## Instructions:

1. Read the code carefully. Understand what the method does and what the spec requires.

2. Add loop invariants for every loop. Common patterns:
   - Bounds: `invariant 0 <= i <= |s|`
   - Accumulator: `invariant acc == F(s[..i])` for recursive ghost functions
   - Sequence slicing: `assert s[..i+1] == s[..i] + [s[i]];` before using F(s[..i+1])
   - Full slice identity: `assert s[..|s|] == s;` after loops that process entire sequences
   - Type preservation: `invariant AllNonNeg(s[..i])` if needed by the spec

3. Add helper lemmas if needed (e.g., SumAppend, induction lemmas).

4. Run dafny verify:
   ```bash
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0034_1102_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0034_1102_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0034_1102_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0034_1102_A/ (create the directory if needed).
