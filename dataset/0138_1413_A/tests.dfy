function DotProduct(a: seq<int>, b: seq<int>): int
  requires |a| == |b|
  decreases |a|
{
  if |a| == 0 then 0
  else DotProduct(a[..|a|-1], b[..|b|-1]) + a[|a|-1] * b[|b|-1]
}

predicate AllNonZero(s: seq<int>) {
  forall i | 0 <= i < |s| :: s[i] != 0
}

predicate AllBounded(s: seq<int>, bound: int) {
  forall i | 0 <= i < |s| :: -bound <= s[i] <= bound
}

predicate ValidSolution(a: seq<int>, b: seq<int>) {
  |a| == |b|
  && AllNonZero(b)
  && AllBounded(b, 100)
  && DotProduct(a, b) == 0
}

method FindSasuke(a: seq<int>) returns (b: seq<int>)
  requires |a| % 2 == 0
  requires AllNonZero(a)
  requires AllBounded(a, 100)
  ensures ValidSolution(a, b)
{
  b := [];
  var i := 0;
  while i < |a|
  {
    if i % 2 == 0 {
      b := b + [a[i + 1]];
    } else {
      b := b + [-a[i - 1]];
    }
    i := i + 1;
  }
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  expect ValidSolution([1, 100], [100, -1]), "spec positive 1";
  expect ValidSolution([1, 1], [1, -1]), "spec positive 3";
  expect ValidSolution([3, -3], [-3, -3]), "spec positive 4";
  expect ValidSolution([5, 10], [10, -5]), "spec positive 7.1";
  expect ValidSolution([-3, 3], [3, 3]), "spec positive 7.2";
  expect ValidSolution([1, -1], [-1, -1]), "spec positive 9.1";
  expect ValidSolution([99, 1], [1, -99]), "spec positive 9.3";
  expect ValidSolution([100, -100], [-100, -100]), "spec positive 10";

  // === SPEC NEGATIVE TESTS ===
  expect !ValidSolution([1, 100], [101, -1]), "spec negative 1";
  expect !ValidSolution([1, 1], [2, -1]), "spec negative 3";
  expect !ValidSolution([3, -3], [-2, -3]), "spec negative 4";
  expect !ValidSolution([5, 10], [11, -5]), "spec negative 7";
  expect !ValidSolution([1, -1], [0, -1]), "spec negative 9";
  expect !ValidSolution([100, -100], [-99, -100]), "spec negative 10";

  // === IMPLEMENTATION TESTS ===
  // Test 1
  var r1 := FindSasuke([1, 100]);
  expect r1 == [100, -1], "impl test 1.1 failed";

  var r2 := FindSasuke([1, 2, 3, 6]);
  expect r2 == [2, -1, 6, -3], "impl test 1.2 failed";

  // Test 2
  var r3 := FindSasuke([-1, 1, 1, 1, 1, 1]);
  expect r3 == [1, 1, 1, -1, 1, -1], "impl test 2.1 failed";

  var r4 := FindSasuke([1, -1, 1, 1, 1, 1]);
  expect r4 == [-1, -1, 1, -1, 1, -1], "impl test 2.2 failed";

  var r5 := FindSasuke([1, 1, -1, 1, 1, 1]);
  expect r5 == [1, -1, 1, 1, 1, -1], "impl test 2.3 failed";

  var r6 := FindSasuke([1, 1, 1, -1, 1, 1]);
  expect r6 == [1, -1, -1, -1, 1, -1], "impl test 2.4 failed";

  var r7 := FindSasuke([1, 1, 1, 1, -1, 1]);
  expect r7 == [1, -1, 1, -1, 1, 1], "impl test 2.5 failed";

  var r8 := FindSasuke([1, 1, 1, 1, 1, -1]);
  expect r8 == [1, -1, 1, -1, -1, -1], "impl test 2.6 failed";

  // Test 3
  var r9 := FindSasuke([1, 1]);
  expect r9 == [1, -1], "impl test 3 failed";

  // Test 4
  var r10 := FindSasuke([3, -3]);
  expect r10 == [-3, -3], "impl test 4 failed";

  // Test 5
  var r11 := FindSasuke([1, 2, 3, 4]);
  expect r11 == [2, -1, 4, -3], "impl test 5 failed";

  // Test 6
  var r12 := FindSasuke([1, 1, 1, 1, 1, 1]);
  expect r12 == [1, -1, 1, -1, 1, -1], "impl test 6 failed";

  // Test 7
  var r13 := FindSasuke([5, 10]);
  expect r13 == [10, -5], "impl test 7.1 failed";

  var r14 := FindSasuke([-3, 3]);
  expect r14 == [3, 3], "impl test 7.2 failed";

  // Test 8
  var r15 := FindSasuke([-1, -2, -3, -4]);
  expect r15 == [-2, 1, -4, 3], "impl test 8 failed";

  // Test 9
  var r16 := FindSasuke([1, -1]);
  expect r16 == [-1, -1], "impl test 9.1 failed";

  var r17 := FindSasuke([2, 3, -2, -3]);
  expect r17 == [3, -2, -3, 2], "impl test 9.2 failed";

  var r18 := FindSasuke([99, 1]);
  expect r18 == [1, -99], "impl test 9.3 failed";

  // Test 10
  var r19 := FindSasuke([100, -100]);
  expect r19 == [-100, -100], "impl test 10 failed";

  // Test 11
  var r20 := FindSasuke([7, -3, 5, 2]);
  expect r20 == [-3, -7, 2, -5], "impl test 11 failed";

  // Test 12
  var r21 := FindSasuke([1, 2]);
  expect r21 == [2, -1], "impl test 12.1 failed";

  var r22 := FindSasuke([3, 4]);
  expect r22 == [4, -3], "impl test 12.2 failed";

  var r23 := FindSasuke([5, 6]);
  expect r23 == [6, -5], "impl test 12.3 failed";

  var r24 := FindSasuke([7, 8]);
  expect r24 == [8, -7], "impl test 12.4 failed";

  var r25 := FindSasuke([9, 10]);
  expect r25 == [10, -9], "impl test 12.5 failed";

  print "All tests passed\n";
}