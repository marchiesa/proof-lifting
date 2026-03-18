predicate CanRearrange(a: seq<int>, b: seq<int>, x: int)
  requires |a| == |b|
  decreases |a|
{
  if |a| == 0 then true
  else exists j | 0 <= j < |b| ::
    a[0] + b[j] <= x &&
    CanRearrange(a[1..], b[..j] + b[j+1..], x)
}

method ArrayRearrangement(a: seq<int>, b: seq<int>, x: int) returns (result: bool)
  requires |a| == |b|
  ensures result == CanRearrange(a, b, x)
{
  var n := |a|;
  var i := 0;
  while i < n
  {
    if a[i] + b[n - 1 - i] > x {
      return false;
    }
    i := i + 1;
  }
  return true;
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // Small inputs only (length 1-3) to keep bounded quantifier enumeration fast.

  // From positive test 2: a=[1], b=[1], x=1 → false
  expect CanRearrange([1], [1], 1) == false, "spec positive 1";

  // From positive test 3: a=[1], b=[1], x=5 → true
  expect CanRearrange([1], [1], 5) == true, "spec positive 2";

  // From positive test 4: a=[5], b=[5], x=5 → false
  expect CanRearrange([5], [5], 5) == false, "spec positive 3";

  // From positive test 5: a=[1,2,3], b=[1,1,2], x=4 → true
  expect CanRearrange([1, 2, 3], [1, 1, 2], 4) == true, "spec positive 4";

  // From positive test 9: a=[1], b=[1], x=2 → true
  expect CanRearrange([1], [1], 2) == true, "spec positive 5";

  // From positive test 1.2/7.1: a=[1,4], b=[2,5], x=6 → true
  expect CanRearrange([1, 4], [2, 5], 6) == true, "spec positive 6";

  // === SPEC NEGATIVE TESTS ===
  // Each verifies that the wrong output does NOT match the spec.

  // From negative test 2: correct=false, wrong=true
  expect CanRearrange([1], [1], 1) != true, "spec negative 1";

  // From negative test 3: correct=true, wrong=false
  expect CanRearrange([1], [1], 5) != false, "spec negative 2";

  // From negative test 4: correct=false, wrong=true
  expect CanRearrange([5], [5], 5) != true, "spec negative 3";

  // From negative test 5: correct=true, wrong=false
  expect CanRearrange([1, 2, 3], [1, 1, 2], 4) != false, "spec negative 4";

  // From negative test 6 (scaled from length 5 to 3): correct=true, wrong=false
  expect CanRearrange([1, 2, 3], [1, 2, 3], 5) != false, "spec negative 5";

  // From negative test 8 (scaled from length 4 to 2): correct=true, wrong=false
  expect CanRearrange([1, 3], [2, 4], 5) != false, "spec negative 6";

  // From negative test 9: correct=true, wrong=false
  expect CanRearrange([1], [1], 2) != false, "spec negative 7";

  // From negative test 10 (scaled from length 6 to 3): correct=true, wrong=false
  expect CanRearrange([1, 2, 3], [1, 2, 3], 4) != false, "spec negative 8";

  // === IMPLEMENTATION TESTS ===
  // Full-size inputs testing the method against expected results.

  var r1 := ArrayRearrangement([1, 2, 3], [1, 1, 2], 4);
  expect r1 == true, "impl test 1 failed";

  var r2 := ArrayRearrangement([1, 4], [2, 5], 6);
  expect r2 == true, "impl test 2 failed";

  var r3 := ArrayRearrangement([1, 2, 3, 4], [1, 2, 3, 4], 4);
  expect r3 == false, "impl test 3 failed";

  var r4 := ArrayRearrangement([5], [5], 5);
  expect r4 == false, "impl test 4 failed";

  var r5 := ArrayRearrangement([1], [1], 1);
  expect r5 == false, "impl test 5 failed";

  var r6 := ArrayRearrangement([1], [1], 5);
  expect r6 == true, "impl test 6 failed";

  var r7 := ArrayRearrangement([1, 2, 3, 4, 5], [1, 2, 3, 4, 5], 10);
  expect r7 == true, "impl test 7 failed";

  var r8 := ArrayRearrangement([1, 3, 5, 7], [1, 2, 4, 6], 8);
  expect r8 == true, "impl test 8 failed";

  var r9 := ArrayRearrangement([1], [1], 2);
  expect r9 == true, "impl test 9 failed";

  var r10 := ArrayRearrangement([1, 1, 2, 3, 4, 5], [1, 2, 3, 4, 5, 6], 7);
  expect r10 == true, "impl test 10 failed";

  var r11 := ArrayRearrangement([1, 5], [2, 3], 10);
  expect r11 == true, "impl test 11 failed";

  var r12 := ArrayRearrangement([1, 2, 3], [1, 2, 3], 6);
  expect r12 == true, "impl test 12 failed";

  var r13 := ArrayRearrangement([10, 20, 30, 40], [5, 10, 15, 20], 50);
  expect r13 == true, "impl test 13 failed";

  var r14 := ArrayRearrangement([1, 2, 3, 4, 5], [1, 2, 3, 4, 5], 5);
  expect r14 == false, "impl test 14 failed";

  var r15 := ArrayRearrangement([1, 2, 3, 4, 5, 6, 7, 8, 9, 10], [2, 4, 6, 8, 10, 11, 12, 13, 14, 15], 20);
  expect r15 == true, "impl test 15 failed";

  print "All tests passed\n";
}