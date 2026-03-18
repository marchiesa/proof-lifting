function TotalSum(n: int): int
  requires n >= 0
{
  n * (n + 1) / 2
}

function Abs(x: int): int
{
  if x >= 0 then x else -x
}

function PartitionSumA(assignment: seq<bool>): int
  decreases |assignment|
{
  if |assignment| == 0 then 0
  else PartitionSumA(assignment[..|assignment|-1]) +
       (if assignment[|assignment|-1] then |assignment| else 0)
}

function PartitionDiff(assignment: seq<bool>, n: int): int
  requires n >= 0
  requires |assignment| == n
{
  Abs(2 * PartitionSumA(assignment) - TotalSum(n))
}

predicate IsSubsetSum(n: nat, target: int)
  decreases n
{
  if target < 0 then false
  else if target == 0 then true
  else if n == 0 then false
  else IsSubsetSum(n - 1, target - n) || IsSubsetSum(n - 1, target)
}

predicate IsOptimalPartitionDiff(n: nat, d: int)
{
  var total := TotalSum(n);
  d >= 0
  && (total - d) % 2 == 0
  && IsSubsetSum(n, (total - d) / 2)
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

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // Small inputs where IsOptimalPartitionDiff can be evaluated at runtime
  expect IsOptimalPartitionDiff(0, 0), "spec positive 1";   // n%4=0, scaled from n=69420
  expect IsOptimalPartitionDiff(1, 1), "spec positive 2";   // n%4=1, matches test 8
  expect IsOptimalPartitionDiff(2, 1), "spec positive 3";   // n%4=2, scaled from n=6
  expect IsOptimalPartitionDiff(3, 0), "spec positive 4";   // n%4=3, matches test 1
  expect IsOptimalPartitionDiff(4, 0), "spec positive 5";   // n%4=0, scaled from n=2000000000
  expect IsOptimalPartitionDiff(5, 1), "spec positive 6";   // n%4=1, matches test 2

  // === SPEC NEGATIVE TESTS ===
  // Small inputs with WRONG outputs — spec must reject these
  expect !IsOptimalPartitionDiff(0, 1), "spec negative 1";  // correct=0, wrong=1
  expect !IsOptimalPartitionDiff(1, 2), "spec negative 2";  // correct=1, wrong=2
  expect !IsOptimalPartitionDiff(2, 2), "spec negative 3";  // correct=1, wrong=2
  expect !IsOptimalPartitionDiff(3, 1), "spec negative 4";  // correct=0, wrong=1
  expect !IsOptimalPartitionDiff(4, 1), "spec negative 5";  // correct=0, wrong=1
  expect !IsOptimalPartitionDiff(5, 2), "spec negative 6";  // correct=1, wrong=2

  // === IMPLEMENTATION TESTS ===
  var r1 := IntegerSequenceDividing(3);
  expect r1 == 0, "impl test 1 failed";

  var r2 := IntegerSequenceDividing(5);
  expect r2 == 1, "impl test 2 failed";

  var r3 := IntegerSequenceDividing(6);
  expect r3 == 1, "impl test 3 failed";

  var r4 := IntegerSequenceDividing(2000000000);
  expect r4 == 0, "impl test 4 failed";

  var r5 := IntegerSequenceDividing(1999999999);
  expect r5 == 0, "impl test 5 failed";

  var r6 := IntegerSequenceDividing(1999999997);
  expect r6 == 1, "impl test 6 failed";

  var r7 := IntegerSequenceDividing(1999999998);
  expect r7 == 1, "impl test 7 failed";

  var r8 := IntegerSequenceDividing(1);
  expect r8 == 1, "impl test 8 failed";

  var r9 := IntegerSequenceDividing(69420);
  expect r9 == 0, "impl test 9 failed";

  var r10 := IntegerSequenceDividing(999999998);
  expect r10 == 1, "impl test 10 failed";

  print "All tests passed\n";
}