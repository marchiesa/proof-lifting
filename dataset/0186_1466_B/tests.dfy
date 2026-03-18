function Pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

function BitAt(mask: nat, i: nat): int
{
  (mask / Pow2(i)) % 2
}

function ApplyChoice(notes: seq<int>, mask: nat): seq<int>
  decreases |notes|
{
  if |notes| == 0 then []
  else ApplyChoice(notes[..|notes|-1], mask) + [notes[|notes|-1] + BitAt(mask, |notes|-1)]
}

function Diversity(s: seq<int>): int
{
  |(set i | 0 <= i < |s| :: s[i])|
}

predicate IsMaxDiversity(notes: seq<int>, d: int)
{
  (exists mask: nat | mask < Pow2(|notes|) :: Diversity(ApplyChoice(notes, mask)) == d)
  &&
  (forall mask: nat | mask < Pow2(|notes|) :: Diversity(ApplyChoice(notes, mask)) <= d)
}

method MaxDiversity(notes: seq<int>) returns (diversity: int)
  requires forall i | 0 <= i < |notes| :: notes[i] > 0
  requires forall i | 0 <= i < |notes| - 1 :: notes[i] <= notes[i + 1]
  ensures IsMaxDiversity(notes, diversity)
{
  var n := |notes|;
  if n == 0 {
    return 0;
  }
  var arr := new int[n];
  var k := 0;
  while k < n {
    arr[k] := notes[k];
    k := k + 1;
  }
  var cnt := 1;
  arr[n - 1] := arr[n - 1] + 1;
  var i := n - 2;
  while i >= 0 {
    if arr[i] == arr[i + 1] {
    } else if arr[i] + 1 == arr[i + 1] {
      cnt := cnt + 1;
    } else {
      arr[i] := arr[i] + 1;
      cnt := cnt + 1;
    }
    i := i - 1;
  }
  return cnt;
}

method Main()
{
  var d: int;

  // ===== SPEC POSITIVE TESTS =====
  // Small inputs (length 1-3) where IsMaxDiversity(notes, correct) should hold

  // From Test 1.4/11.5: [1] -> 1
  expect IsMaxDiversity([1], 1), "spec positive 1";
  // From Test 3: [7] -> 1
  expect IsMaxDiversity([7], 1), "spec positive 2";
  // From Test 8.2: [50] -> 1, scaled to [3]
  expect IsMaxDiversity([3], 1), "spec positive 3";
  // From Test 11.1: [1, 2] -> 2
  expect IsMaxDiversity([1, 2], 2), "spec positive 4";
  // From Test 11.2: [1, 1] -> 2
  expect IsMaxDiversity([1, 1], 2), "spec positive 5";
  // From Test 1.2: [4, 4] -> 2, scaled to [2, 2]
  expect IsMaxDiversity([2, 2], 2), "spec positive 6";
  // From Test 6.1: [3, 3] -> 2
  expect IsMaxDiversity([3, 3], 2), "spec positive 7";
  // From Test 2.2/6.3: [1, 1, 1] -> 2
  expect IsMaxDiversity([1, 1, 1], 2), "spec positive 8";
  // From Test 11.3: [2, 2, 2] -> 2
  expect IsMaxDiversity([2, 2, 2], 2), "spec positive 9";
  // From Test 6.2: [1, 2, 3] -> 3
  expect IsMaxDiversity([1, 2, 3], 3), "spec positive 10";
  // From Test 9.2: [1, 1, 2] -> 3
  expect IsMaxDiversity([1, 1, 2], 3), "spec positive 11";

  // ===== SPEC NEGATIVE TESTS =====
  // Small inputs where IsMaxDiversity(notes, wrong) should NOT hold

  // From Neg 3: [7] wrong=2 (correct=1), scaled to [1]
  expect !IsMaxDiversity([1], 2), "spec negative 1";
  // From Neg 6: [3, 3] wrong=3 (correct=2)
  expect !IsMaxDiversity([3, 3], 3), "spec negative 2";
  // From Neg 1: [1,2,2,2,5,6] wrong=6, scaled to [1, 2] wrong=3
  expect !IsMaxDiversity([1, 2], 3), "spec negative 3";
  // From Neg 2: [1,2,3,4] wrong=5, scaled to [1, 2, 3] wrong=4
  expect !IsMaxDiversity([1, 2, 3], 4), "spec negative 4";
  // From Neg 5: [1,1,2,3,3,4,5,5,6,7] wrong=9, scaled to [1, 1, 1] wrong=3
  expect !IsMaxDiversity([1, 1, 1], 3), "spec negative 5";
  // From Neg 4: [1,1,2,3,5,5] wrong=7, scaled to [1, 1, 2] wrong=4
  expect !IsMaxDiversity([1, 1, 2], 4), "spec negative 6";
  // From Neg 7: [1,1,1,1,1,1,1] wrong=3, scaled to [2, 2, 2] wrong=3
  expect !IsMaxDiversity([2, 2, 2], 3), "spec negative 7";
  // From Neg 9: [1,1,2,2,3,3,4,4] wrong=6, scaled to [1, 1] wrong=3
  expect !IsMaxDiversity([1, 1], 3), "spec negative 8";
  // From Neg 8: [1,2,2,3,4] wrong=6, scaled to [2, 2] wrong=3
  expect !IsMaxDiversity([2, 2], 3), "spec negative 9";
  // From Neg 10: [1,..,10] wrong=11, scaled to [1, 1, 2] wrong=2 (too low)
  expect !IsMaxDiversity([1, 1, 2], 2), "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====

  // Test 1
  d := MaxDiversity([1, 2, 2, 2, 5, 6]);
  expect d == 5, "impl test 1.1 failed";
  d := MaxDiversity([4, 4]);
  expect d == 2, "impl test 1.2 failed";
  d := MaxDiversity([1, 1, 3, 4, 4, 5]);
  expect d == 6, "impl test 1.3 failed";
  d := MaxDiversity([1]);
  expect d == 1, "impl test 1.4 failed";
  d := MaxDiversity([1, 1, 1, 2, 2, 2]);
  expect d == 3, "impl test 1.5 failed";

  // Test 2
  d := MaxDiversity([1, 2, 3, 4]);
  expect d == 4, "impl test 2.1 failed";
  d := MaxDiversity([1, 1, 1]);
  expect d == 2, "impl test 2.2 failed";
  d := MaxDiversity([2, 2, 4, 4, 6]);
  expect d == 5, "impl test 2.3 failed";

  // Test 3
  d := MaxDiversity([7]);
  expect d == 1, "impl test 3.1 failed";

  // Test 4
  d := MaxDiversity([1, 1, 2, 3, 5, 5]);
  expect d == 6, "impl test 4.1 failed";
  d := MaxDiversity([1, 1, 1, 1]);
  expect d == 2, "impl test 4.2 failed";

  // Test 5
  d := MaxDiversity([1, 1, 2, 3, 3, 4, 5, 5, 6, 7]);
  expect d == 8, "impl test 5.1 failed";

  // Test 6
  d := MaxDiversity([3, 3]);
  expect d == 2, "impl test 6.1 failed";
  d := MaxDiversity([1, 2, 3]);
  expect d == 3, "impl test 6.2 failed";
  d := MaxDiversity([1, 1, 1, 1, 1]);
  expect d == 2, "impl test 6.3 failed";
  d := MaxDiversity([2, 4, 6, 8]);
  expect d == 4, "impl test 6.4 failed";

  // Test 7
  d := MaxDiversity([1, 1, 1, 1, 1, 1, 1]);
  expect d == 2, "impl test 7.1 failed";

  // Test 8
  d := MaxDiversity([1, 2, 2, 3, 4]);
  expect d == 5, "impl test 8.1 failed";
  d := MaxDiversity([50]);
  expect d == 1, "impl test 8.2 failed";
  d := MaxDiversity([1, 3, 3, 5, 5, 5]);
  expect d == 5, "impl test 8.3 failed";

  // Test 9
  d := MaxDiversity([1, 1, 2, 2, 3, 3, 4, 4]);
  expect d == 5, "impl test 9.1 failed";
  d := MaxDiversity([1, 1, 2]);
  expect d == 3, "impl test 9.2 failed";

  // Test 10
  d := MaxDiversity([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
  expect d == 10, "impl test 10.1 failed";

  // Test 11
  d := MaxDiversity([1, 2]);
  expect d == 2, "impl test 11.1 failed";
  d := MaxDiversity([1, 1]);
  expect d == 2, "impl test 11.2 failed";
  d := MaxDiversity([2, 2, 2]);
  expect d == 2, "impl test 11.3 failed";
  d := MaxDiversity([1, 1, 3, 3]);
  expect d == 4, "impl test 11.4 failed";
  d := MaxDiversity([1]);
  expect d == 1, "impl test 11.5 failed";

  print "All tests passed\n";
}