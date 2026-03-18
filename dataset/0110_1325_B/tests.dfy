// Spec functions (non-ghost, testable at runtime)
function Repeat(a: seq<int>, n: nat): seq<int>
  decreases n
{
  if n == 0 then [] else a + Repeat(a, n - 1)
}

predicate HasIncSubseqFrom(b: seq<int>, k: nat, minVal: int)
  decreases |b|
{
  if k == 0 then true
  else if |b| < k then false
  else
    (b[0] > minVal && HasIncSubseqFrom(b[1..], k - 1, b[0]))
    ||
    HasIncSubseqFrom(b[1..], k, minVal)
}

predicate HasIncSubseq(b: seq<int>, k: nat)
  decreases |b|
{
  if k == 0 then true
  else if |b| < k then false
  else
    HasIncSubseqFrom(b[1..], k - 1, b[0])
    ||
    HasIncSubseq(b[1..], k)
}

function LISSearch(b: seq<int>, maxK: nat): nat
  decreases maxK
{
  if maxK == 0 then 0
  else if HasIncSubseq(b, maxK) then maxK
  else LISSearch(b, maxK - 1)
}

function LISLength(b: seq<int>): nat
{
  LISSearch(b, |b|)
}

// Implementation
method CopyCopyCopyCopyCopy(a: seq<int>) returns (result: int)
  ensures result == LISLength(Repeat(a, |a|))
{
  var n := |a|;
  if n == 0 {
    return 0;
  }
  var arr := new int[n];
  var i := 0;
  while i < n
  {
    arr[i] := a[i];
    i := i + 1;
  }
  var j := 1;
  while j < n
  {
    var key := arr[j];
    var k := j - 1;
    while k >= 0 && arr[k] > key
    {
      arr[k + 1] := arr[k];
      k := k - 1;
    }
    arr[k + 1] := key;
    j := j + 1;
  }
  var ans := n;
  var m := 0;
  while m < n - 1
  {
    if arr[m + 1] == arr[m] {
      ans := ans - 1;
    }
    m := m + 1;
  }
  return ans;
}

method Main()
{
  // ========== SPEC POSITIVE TESTS ==========
  // ensures: result == LISLength(Repeat(a, |a|))
  // Using small inputs (length 1-3) to keep recursive spec evaluation fast.

  // From Test 1a: [3,2,1] -> 3  (Repeat produces length 9)
  expect LISLength(Repeat([3, 2, 1], 3)) == 3, "spec positive 1";
  // From Test 2b: [2] -> 1  (Repeat produces length 1)
  expect LISLength(Repeat([2], 1)) == 1, "spec positive 2";
  // From Test 3b: [1,2,5] -> 3  (Repeat produces length 9)
  expect LISLength(Repeat([1, 2, 5], 3)) == 3, "spec positive 3";
  // From Test 5: [1,1,274005660] -> 2  (Repeat produces length 9)
  expect LISLength(Repeat([1, 1, 274005660], 3)) == 2, "spec positive 4";
  // From Test 6a: [1,1] -> 1  (Repeat produces length 4)
  expect LISLength(Repeat([1, 1], 2)) == 1, "spec positive 5";
  // From Test 6b: [1] -> 1  (Repeat produces length 1)
  expect LISLength(Repeat([1], 1)) == 1, "spec positive 6";
  // From Test 7b: [1,2,3] -> 3  (Repeat produces length 9)
  expect LISLength(Repeat([1, 2, 3], 3)) == 3, "spec positive 7";
  // From Test 8a: [1,1,1] -> 1  (Repeat produces length 9)
  expect LISLength(Repeat([1, 1, 1], 3)) == 1, "spec positive 8";

  // ========== SPEC NEGATIVE TESTS ==========
  // Each uses the WRONG output and checks the spec rejects it.

  // From Neg 1: [3,2,1] correct=3, wrong=4
  expect LISLength(Repeat([3, 2, 1], 3)) != 4, "spec negative 1";
  // From Neg 2 (scaled [6,6,8,8,6,6,6]->wrong=3 to [1,1,2]->wrong=3): correct=2
  expect LISLength(Repeat([1, 1, 2], 3)) != 3, "spec negative 2";
  // From Neg 4 (scaled [1,2,3,4,5]->wrong=6 to [1,2,3]->wrong=4): correct=3
  expect LISLength(Repeat([1, 2, 3], 3)) != 4, "spec negative 3";
  // From Neg 5: [1,1,274005660] correct=2, wrong=3
  expect LISLength(Repeat([1, 1, 274005660], 3)) != 3, "spec negative 4";
  // From Neg 6: [1,1] correct=1, wrong=2
  expect LISLength(Repeat([1, 1], 2)) != 2, "spec negative 5";
  // From Neg 7 (scaled [1,3,3,3]->wrong=3 to [1,3,3]->wrong=3): correct=2
  expect LISLength(Repeat([1, 3, 3], 3)) != 3, "spec negative 6";
  // From Neg 8: [1,1,1] correct=1, wrong=2
  expect LISLength(Repeat([1, 1, 1], 3)) != 2, "spec negative 7";
  // From Neg 9 (scaled [1,3,4,5,2]->wrong=6 to [1,3,2]->wrong=4): correct=3
  expect LISLength(Repeat([1, 3, 2], 3)) != 4, "spec negative 8";
  // From Neg 3 (scaled [5,5,5,5,5]->wrong=2 to [2,2]->wrong=2): correct=1
  expect LISLength(Repeat([2, 2], 2)) != 2, "spec negative 9";

  // ========== IMPLEMENTATION TESTS ==========

  // Test 1
  var r1 := CopyCopyCopyCopyCopy([3, 2, 1]);
  expect r1 == 3, "impl test 1a failed";
  var r2 := CopyCopyCopyCopyCopy([3, 1, 4, 1, 5, 9]);
  expect r2 == 5, "impl test 1b failed";

  // Test 2
  var r3 := CopyCopyCopyCopyCopy([6, 6, 8, 8, 6, 6, 6]);
  expect r3 == 2, "impl test 2a failed";
  var r4 := CopyCopyCopyCopyCopy([2]);
  expect r4 == 1, "impl test 2b failed";
  var r5 := CopyCopyCopyCopyCopy([4, 5, 9, 8, 7]);
  expect r5 == 5, "impl test 2c failed";
  var r6 := CopyCopyCopyCopyCopy([1, 2, 7, 1, 6, 10, 2]);
  expect r6 == 5, "impl test 2d failed";

  // Test 3
  var r7 := CopyCopyCopyCopyCopy([5, 5, 5, 5, 5]);
  expect r7 == 1, "impl test 3a failed";
  var r8 := CopyCopyCopyCopyCopy([1, 2, 5]);
  expect r8 == 3, "impl test 3b failed";

  // Test 4
  var r9 := CopyCopyCopyCopyCopy([1, 2, 3, 4, 5]);
  expect r9 == 5, "impl test 4a failed";
  var r10 := CopyCopyCopyCopyCopy([2, 3, 4, 5]);
  expect r10 == 4, "impl test 4b failed";

  // Test 5
  var r11 := CopyCopyCopyCopyCopy([1, 1, 274005660]);
  expect r11 == 2, "impl test 5 failed";

  // Test 6
  var r12 := CopyCopyCopyCopyCopy([1, 1]);
  expect r12 == 1, "impl test 6a failed";
  var r13 := CopyCopyCopyCopyCopy([1]);
  expect r13 == 1, "impl test 6b failed";

  // Test 7
  var r14 := CopyCopyCopyCopyCopy([1, 3, 3, 3]);
  expect r14 == 2, "impl test 7a failed";
  var r15 := CopyCopyCopyCopyCopy([1, 2, 3]);
  expect r15 == 3, "impl test 7b failed";

  // Test 8
  var r16 := CopyCopyCopyCopyCopy([1, 1, 1]);
  expect r16 == 1, "impl test 8a failed";
  var r17 := CopyCopyCopyCopyCopy([1, 1]);
  expect r17 == 1, "impl test 8b failed";

  // Test 9
  var r18 := CopyCopyCopyCopyCopy([1, 3, 4, 5, 2]);
  expect r18 == 5, "impl test 9 failed";

  print "All tests passed\n";
}