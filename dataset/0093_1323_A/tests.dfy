function Pow2(n: int): int
  decreases if n < 0 then 0 else n
{
  if n <= 0 then 1 else 2 * Pow2(n - 1)
}

predicate BitSet(mask: int, i: int)
{
  mask >= 0 && i >= 0 && (mask / Pow2(i)) % 2 == 1
}

function MaskedSum(a: seq<int>, mask: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else MaskedSum(a[..|a| - 1], mask) + (if BitSet(mask, |a| - 1) then a[|a| - 1] else 0)
}

predicate HasEvenSubset(a: seq<int>)
{
  exists mask: int | 1 <= mask < Pow2(|a|) :: MaskedSum(a, mask) % 2 == 0
}

predicate Distinct(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] != s[j]
}

predicate ValidIndices(indices: seq<int>, n: int)
{
  |indices| > 0 &&
  Distinct(indices) &&
  (forall i | 0 <= i < |indices| :: 1 <= indices[i] <= n)
}

function IndexSum(a: seq<int>, indices: seq<int>): int
  decreases |indices|
{
  if |indices| == 0 then 0
  else
    var idx := indices[|indices| - 1];
    IndexSum(a, indices[..|indices| - 1]) + (if 1 <= idx <= |a| then a[idx - 1] else 0)
}

predicate Spec(a: seq<int>, indices: seq<int>)
{
  ((indices == [-1]) <==> !HasEvenSubset(a)) &&
  (indices != [-1] ==> ValidIndices(indices, |a|) && IndexSum(a, indices) % 2 == 0)
}

method EvenSubsetSum(a: seq<int>) returns (indices: seq<int>)
  requires |a| >= 1
  requires forall i | 0 <= i < |a| :: a[i] > 0
  ensures (indices == [-1]) <==> !HasEvenSubset(a)
  ensures indices != [-1] ==> ValidIndices(indices, |a|) && IndexSum(a, indices) % 2 == 0
{
  var n := |a|;
  if n == 1 && a[0] % 2 == 1 {
    indices := [-1];
  } else {
    var ind := -1;
    var ind2 := -1;
    var ind3 := -1;
    var j := 0;
    while j < n
    {
      if a[j] % 2 == 0 {
        ind := j;
      } else if ind2 == -1 {
        ind2 := j;
      } else {
        ind3 := j;
      }
      j := j + 1;
    }
    if ind == -1 {
      indices := [ind2 + 1, ind3 + 1];
    } else {
      indices := [ind + 1];
    }
  }
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Verify the spec accepts correct (input, output) pairs

  // From Test 1 (all length <= 3)
  expect Spec([1, 4, 3], [2]), "spec positive 1";
  expect Spec([15], [-1]), "spec positive 2";
  expect Spec([3, 5], [1, 2]), "spec positive 3";

  // From Test 2
  expect Spec([1, 1], [1, 2]), "spec positive 4";

  // From Test 3 (all length 1-3, values 1-2)
  expect Spec([2], [1]), "spec positive 5";
  expect Spec([1], [-1]), "spec positive 6";
  expect Spec([2, 2], [2]), "spec positive 7";
  expect Spec([2, 1], [1]), "spec positive 8";
  expect Spec([1, 2], [2]), "spec positive 9";
  expect Spec([1, 1], [1, 2]), "spec positive 10";
  expect Spec([2, 2, 2], [3]), "spec positive 11";
  expect Spec([2, 2, 1], [2]), "spec positive 12";
  expect Spec([2, 1, 2], [3]), "spec positive 13";
  expect Spec([2, 1, 1], [1]), "spec positive 14";
  expect Spec([1, 2, 2], [3]), "spec positive 15";
  expect Spec([1, 2, 1], [2]), "spec positive 16";
  expect Spec([1, 1, 2], [3]), "spec positive 17";
  expect Spec([1, 1, 1], [1, 3]), "spec positive 18";

  // ===== SPEC NEGATIVE TESTS =====
  // Verify the spec rejects wrong (input, output) pairs

  // From Negative 1: a=[1,4,3], wrong count=2 → duplicate indices [2,2] (Distinct fails)
  expect !Spec([1, 4, 3], [2, 2]), "spec negative 1";

  // From Negative 2: a=[1,1], wrong count=3 → indices [1,2,1] (Distinct fails)
  expect !Spec([1, 1], [1, 2, 1]), "spec negative 2";

  // From Negative 3: a=[2], wrong count=2 → duplicate indices [1,1] (Distinct fails)
  expect !Spec([2], [1, 1]), "spec negative 3";

  // Additional: a=[2,1], returning [-1] when even subset exists (biconditional fails)
  expect !Spec([2, 1], [-1]), "spec negative 4";

  // a=[1,2], wrong index [1] gives odd sum (IndexSum=1, not even)
  expect !Spec([1, 2], [1]), "spec negative 5";

  // a=[1,1,1], wrong index [1] gives odd sum (IndexSum=1, not even)
  expect !Spec([1, 1, 1], [1]), "spec negative 6";

  // a=[2,2], returning [-1] when even subset exists (biconditional fails)
  expect !Spec([2, 2], [-1]), "spec negative 7";

  // ===== IMPLEMENTATION TESTS =====
  // Call the method and check correct output

  // Test 1
  var r1 := EvenSubsetSum([1, 4, 3]);
  expect r1 == [2], "impl test 1 failed";

  var r2 := EvenSubsetSum([15]);
  expect r2 == [-1], "impl test 2 failed";

  var r3 := EvenSubsetSum([3, 5]);
  expect r3 == [1, 2], "impl test 3 failed";

  // Test 2
  var r4 := EvenSubsetSum([1, 1]);
  expect r4 == [1, 2], "impl test 4 failed";

  // Test 3
  var r5 := EvenSubsetSum([2]);
  expect r5 == [1], "impl test 5 failed";

  var r6 := EvenSubsetSum([1]);
  expect r6 == [-1], "impl test 6 failed";

  var r7 := EvenSubsetSum([2, 2]);
  expect r7 == [2], "impl test 7 failed";

  var r8 := EvenSubsetSum([2, 1]);
  expect r8 == [1], "impl test 8 failed";

  var r9 := EvenSubsetSum([1, 2]);
  expect r9 == [2], "impl test 9 failed";

  var r10 := EvenSubsetSum([1, 1]);
  expect r10 == [1, 2], "impl test 10 failed";

  var r11 := EvenSubsetSum([2, 2, 2]);
  expect r11 == [3], "impl test 11 failed";

  var r12 := EvenSubsetSum([2, 2, 1]);
  expect r12 == [2], "impl test 12 failed";

  var r13 := EvenSubsetSum([2, 1, 2]);
  expect r13 == [3], "impl test 13 failed";

  var r14 := EvenSubsetSum([2, 1, 1]);
  expect r14 == [1], "impl test 14 failed";

  var r15 := EvenSubsetSum([1, 2, 2]);
  expect r15 == [3], "impl test 15 failed";

  var r16 := EvenSubsetSum([1, 2, 1]);
  expect r16 == [2], "impl test 16 failed";

  var r17 := EvenSubsetSum([1, 1, 2]);
  expect r17 == [3], "impl test 17 failed";

  var r18 := EvenSubsetSum([1, 1, 1]);
  expect r18 == [1, 3], "impl test 18 failed";

  print "All tests passed\n";
}