// --- Specification functions ---

function Pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

function GetBit(mask: nat, i: nat): bool
{
  (mask / Pow2(i)) % 2 == 1
}

function MaskSelectedCount(mask: nat, n: nat): nat
  decreases n
{
  if n == 0 then 0
  else MaskSelectedCount(mask, n - 1) + (if GetBit(mask, n - 1) then 1 else 0)
}

function SubseqSum(a: seq<int>, mask: nat): int
  decreases |a|
{
  if |a| == 0 then 0
  else
    SubseqSum(a[..|a|-1], mask) + (if GetBit(mask, (|a| - 1) as nat) then a[|a|-1] else 0)
}

function PerformOp(a: seq<int>, mask: nat): seq<int>
{
  var c := MaskSelectedCount(mask, |a| as nat);
  if c == 0 then a
  else
    var s := SubseqSum(a, mask);
    RemoveAboveAvg(a, mask, s, c)
}

function RemoveAboveAvg(a: seq<int>, mask: nat, total: int, count: nat): seq<int>
  requires count > 0
  decreases |a|
{
  if |a| == 0 then []
  else
    var i: nat := (|a| - 1) as nat;
    var rest := RemoveAboveAvg(a[..|a|-1], mask, total, count);
    var selected := GetBit(mask, i);
    var aboveAvg := a[i] * (count as int) > total;
    if selected && aboveAvg then rest else rest + [a[i]]
}

predicate CanReachSize(a: seq<int>, sz: int, steps: nat)
  decreases steps
{
  if |a| == sz then true
  else if |a| < sz || sz < 0 then false
  else if steps == 0 then false
  else
    exists mask: nat | 1 <= mask < Pow2(|a| as nat) ::
      var next := PerformOp(a, mask);
      |next| < |a| &&
      CanReachSize(next, sz, steps - 1)
}

// --- Implementation ---

method EshagLovesBigArrays(a: seq<int>) returns (deleted: int)
  requires |a| >= 1
  ensures 0 <= deleted <= |a|
  ensures CanReachSize(a, |a| - deleted, |a| as nat)
  ensures forall k: int {:trigger CanReachSize(a, |a| - k, |a| as nat)} | deleted < k <= |a| :: !CanReachSize(a, |a| - k, |a| as nat)
{
  var mi := a[0];
  var i := 1;
  while i < |a|
  {
    if a[i] < mi {
      mi := a[i];
    }
    i := i + 1;
  }

  var c := 0;
  i := 0;
  while i < |a|
  {
    if a[i] == mi {
      c := c + 1;
    }
    i := i + 1;
  }

  deleted := |a| - c;
}

method Main()
{
  var result: int;

  // ============================================================
  // SPEC POSITIVE TESTS — CanReachSize(a, |a|-deleted, |a| as nat)
  // Small inputs only (length 1-3) to keep quantifier enumeration fast
  // ============================================================

  // Test 3: [5] -> deleted=0, target size 1
  expect CanReachSize([5], 1, 1), "spec positive 3";

  // Test 2: [1,2] -> deleted=1, target size 1
  expect CanReachSize([1, 2], 1, 2), "spec positive 2";

  // Test 10c: [1,1] -> deleted=0, target size 2
  expect CanReachSize([1, 1], 2, 2), "spec positive 10c";

  // Test 5: [1,2,3] -> deleted=2, target size 1
  expect CanReachSize([1, 2, 3], 1, 3), "spec positive 5";

  // Test 10a: [1,1,2] -> deleted=1, target size 2
  expect CanReachSize([1, 1, 2], 2, 3), "spec positive 10a";

  // Test 9 (scaled [1,50]->[1,5]): deleted=1, target size 1
  expect CanReachSize([1, 5], 1, 2), "spec positive 9";

  // Test 7 (scaled [3,3,3,3]->[3,3]): deleted=0, target size 2
  expect CanReachSize([3, 3], 2, 2), "spec positive 7";

  // Test 12a (scaled [2,2,2,2,3]->[2,2,3]): deleted=1, target size 2
  expect CanReachSize([2, 2, 3], 2, 3), "spec positive 12a";

  // Optimality ensures: forall k > deleted: !CanReachSize(a, |a|-k, |a| as nat)
  // Unrolled for each k in range (deleted, |a|]
  expect !CanReachSize([5], 0, 1), "spec positive 3 opt k=1";
  expect !CanReachSize([1, 2], 0, 2), "spec positive 2 opt k=2";
  expect !CanReachSize([1, 1], 1, 2), "spec positive 10c opt k=1";
  expect !CanReachSize([1, 1], 0, 2), "spec positive 10c opt k=2";
  expect !CanReachSize([1, 2, 3], 0, 3), "spec positive 5 opt k=3";
  expect !CanReachSize([1, 1, 2], 1, 3), "spec positive 10a opt k=2";
  expect !CanReachSize([1, 1, 2], 0, 3), "spec positive 10a opt k=3";
  expect !CanReachSize([1, 5], 0, 2), "spec positive 9 opt k=2";
  expect !CanReachSize([3, 3], 1, 2), "spec positive 7 opt k=1";
  expect !CanReachSize([3, 3], 0, 2), "spec positive 7 opt k=2";
  expect !CanReachSize([2, 2, 3], 1, 3), "spec positive 12a opt k=2";
  expect !CanReachSize([2, 2, 3], 0, 3), "spec positive 12a opt k=3";

  // ============================================================
  // SPEC NEGATIVE TESTS — !CanReachSize(a, |a|-wrong_deleted, |a| as nat)
  // Wrong deleted > correct deleted, so claimed target size is unreachable
  // ============================================================

  // Neg 3: [5] -> wrong=1, target size 0
  expect !CanReachSize([5], 0, 1), "spec negative 3";

  // Neg 2: [1,2] -> wrong=2, target size 0
  expect !CanReachSize([1, 2], 0, 2), "spec negative 2";

  // Neg 5: [1,2,3] -> wrong=3, target size 0
  expect !CanReachSize([1, 2, 3], 0, 3), "spec negative 5";

  // Neg 9 (scaled [1,50]->[1,5]): wrong=2, target size 0
  expect !CanReachSize([1, 5], 0, 2), "spec negative 9";

  // Neg 10: [1,1,2] -> wrong=2, target size 1
  expect !CanReachSize([1, 1, 2], 1, 3), "spec negative 10";

  // Neg 4 (scaled [1,1,1,1,1]->[1,1]): wrong=1, target size 1
  expect !CanReachSize([1, 1], 1, 2), "spec negative 4";

  // Neg 7 (scaled [3,3,3,3]->[3,3]): wrong=1, target size 1
  expect !CanReachSize([3, 3], 1, 2), "spec negative 7";

  // Neg 8 (scaled [1..7]->[1,2,3]): wrong=3, target size 0
  expect !CanReachSize([1, 2, 3], 0, 3), "spec negative 8";

  // Neg 1 (scaled [1,1,1,2,2,3]->[1,1,2]): wrong=2, target size 1
  expect !CanReachSize([1, 1, 2], 1, 3), "spec negative 1";

  // Neg 6 (scaled, same pattern as Neg 1): wrong=2, target size 1
  expect !CanReachSize([1, 1, 3], 1, 3), "spec negative 6";

  // ============================================================
  // IMPLEMENTATION TESTS — full-size inputs, method is fast
  // ============================================================

  // Test 1
  result := EshagLovesBigArrays([1, 1, 1, 2, 2, 3]);
  expect result == 3, "impl test 1a failed";
  result := EshagLovesBigArrays([9, 9, 9, 9, 9, 9]);
  expect result == 0, "impl test 1b failed";
  result := EshagLovesBigArrays([6, 4, 1, 1, 4, 1]);
  expect result == 3, "impl test 1c failed";

  // Test 2
  result := EshagLovesBigArrays([1, 2]);
  expect result == 1, "impl test 2 failed";

  // Test 3
  result := EshagLovesBigArrays([5]);
  expect result == 0, "impl test 3 failed";

  // Test 4
  result := EshagLovesBigArrays([1, 1, 1, 1, 1]);
  expect result == 0, "impl test 4 failed";

  // Test 5
  result := EshagLovesBigArrays([1, 2, 3]);
  expect result == 2, "impl test 5 failed";

  // Test 6
  result := EshagLovesBigArrays([1, 1, 1, 2, 2, 3]);
  expect result == 3, "impl test 6 failed";

  // Test 7
  result := EshagLovesBigArrays([3, 3, 3, 3]);
  expect result == 0, "impl test 7 failed";

  // Test 8
  result := EshagLovesBigArrays([1, 2, 3, 4, 5, 6, 7]);
  expect result == 6, "impl test 8 failed";

  // Test 9
  result := EshagLovesBigArrays([1, 50]);
  expect result == 1, "impl test 9 failed";

  // Test 10
  result := EshagLovesBigArrays([1, 1, 2]);
  expect result == 1, "impl test 10a failed";
  result := EshagLovesBigArrays([5, 5, 5, 10]);
  expect result == 1, "impl test 10b failed";
  result := EshagLovesBigArrays([1, 1]);
  expect result == 0, "impl test 10c failed";

  // Test 11
  result := EshagLovesBigArrays([1, 1, 1, 1, 1, 1, 1, 1, 1, 50]);
  expect result == 1, "impl test 11 failed";

  // Test 12
  result := EshagLovesBigArrays([2, 2, 2, 2, 3]);
  expect result == 1, "impl test 12a failed";
  result := EshagLovesBigArrays([6, 4, 1, 1, 4, 1]);
  expect result == 3, "impl test 12b failed";

  print "All tests passed\n";
}