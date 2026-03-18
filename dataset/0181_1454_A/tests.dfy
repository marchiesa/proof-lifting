predicate InRange(p: seq<int>, n: int)
{
  forall i | 0 <= i < |p| :: 1 <= p[i] <= n
}

predicate AllDistinct(p: seq<int>)
{
  forall i, j | 0 <= i < |p| && 0 <= j < |p| && i != j :: p[i] != p[j]
}

predicate IsPermutation(p: seq<int>, n: int)
{
  |p| == n && InRange(p, n) && AllDistinct(p)
}

predicate NoFixedPoint(p: seq<int>)
{
  forall i | 0 <= i < |p| :: p[i] != i + 1
}

method SpecialPermutation(n: int) returns (p: seq<int>)
  requires n > 1
  ensures IsPermutation(p, n)
  ensures NoFixedPoint(p)
{
  p := [n];
  var i := 1;
  while i < n {
    p := p + [i];
    i := i + 1;
  }
}

method BuildExpected(n: int) returns (e: seq<int>)
{
  e := [n];
  var i := 1;
  while i < n {
    e := e + [i];
    i := i + 1;
  }
}

method Main()
{
  var p: seq<int>;
  var e: seq<int>;

  // =====================
  // SPEC POSITIVE tests
  // =====================
  // ensures: IsPermutation(p, n) && NoFixedPoint(p)

  // From positive test 1/3/9: n=2, correct=[2,1]
  expect IsPermutation([2, 1], 2) && NoFixedPoint([2, 1]), "spec positive 1";

  // From positive test 1/4: n=5, correct=[5,1,2,3,4]
  expect IsPermutation([5, 1, 2, 3, 4], 5) && NoFixedPoint([5, 1, 2, 3, 4]), "spec positive 2";

  // From positive test 5/12: n=3, correct=[3,1,2]
  expect IsPermutation([3, 1, 2], 3) && NoFixedPoint([3, 1, 2]), "spec positive 3";

  // From positive test 5/7: n=4, correct=[4,1,2,3]
  expect IsPermutation([4, 1, 2, 3], 4) && NoFixedPoint([4, 1, 2, 3]), "spec positive 4";

  // From positive test 7: n=6, correct=[6,1,2,3,4,5]
  expect IsPermutation([6, 1, 2, 3, 4, 5], 6) && NoFixedPoint([6, 1, 2, 3, 4, 5]), "spec positive 5";

  // From positive test 8: n=7, correct=[7,1,2,3,4,5,6]
  expect IsPermutation([7, 1, 2, 3, 4, 5, 6], 7) && NoFixedPoint([7, 1, 2, 3, 4, 5, 6]), "spec positive 6";

  // =====================
  // SPEC NEGATIVE tests
  // =====================
  // Wrong outputs should be rejected by the spec

  // Neg 1: n=2, wrong=[3,1] (first element 2->3, out of range)
  expect !(IsPermutation([3, 1], 2) && NoFixedPoint([3, 1])), "spec negative 1";

  // Neg 2: n=2 (first wrong input from 100-input test), wrong=[3,1]
  expect !(IsPermutation([3, 1], 2) && NoFixedPoint([3, 1])), "spec negative 2";

  // Neg 3: n=2, wrong=[3,1]
  expect !(IsPermutation([3, 1], 2) && NoFixedPoint([3, 1])), "spec negative 3";

  // Neg 4: n=5, wrong=[6,1,2,3,4] (first element 5->6, out of range)
  expect !(IsPermutation([6, 1, 2, 3, 4], 5) && NoFixedPoint([6, 1, 2, 3, 4])), "spec negative 4";

  // Neg 5: n=2, wrong=[3,1] (first input of 3-input test)
  expect !(IsPermutation([3, 1], 2) && NoFixedPoint([3, 1])), "spec negative 5";

  // Neg 6: scaled from n=10 wrong=[11,...] to n=3 wrong=[4,1,2]
  expect !(IsPermutation([4, 1, 2], 3) && NoFixedPoint([4, 1, 2])), "spec negative 6";

  // Neg 7: n=2, wrong=[3,1] (first input of 5-input test)
  expect !(IsPermutation([3, 1], 2) && NoFixedPoint([3, 1])), "spec negative 7";

  // Neg 8: n=7, wrong=[8,1,2,3,4,5,6] (first element 7->8, out of range)
  expect !(IsPermutation([8, 1, 2, 3, 4, 5, 6], 7) && NoFixedPoint([8, 1, 2, 3, 4, 5, 6])), "spec negative 8";

  // Neg 9: n=2, wrong=[3,1]
  expect !(IsPermutation([3, 1], 2) && NoFixedPoint([3, 1])), "spec negative 9";

  // Neg 10: scaled from n=50 wrong=[51,...] to n=3 wrong=[4,1,2]
  expect !(IsPermutation([4, 1, 2], 3) && NoFixedPoint([4, 1, 2])), "spec negative 10";

  // =====================
  // IMPLEMENTATION tests
  // =====================

  // Test 1: n=2, n=5
  p := SpecialPermutation(2);
  e := BuildExpected(2);
  expect p == e, "impl test 1 failed for n=2";
  p := SpecialPermutation(5);
  e := BuildExpected(5);
  expect p == e, "impl test 1 failed for n=5";

  // Test 2: n=2..100 then n=36
  var n := 2;
  while n <= 100 {
    p := SpecialPermutation(n);
    e := BuildExpected(n);
    expect p == e, "impl test 2 failed";
    n := n + 1;
  }
  p := SpecialPermutation(36);
  e := BuildExpected(36);
  expect p == e, "impl test 2 failed for n=36";

  // Test 3: n=2
  p := SpecialPermutation(2);
  e := BuildExpected(2);
  expect p == e, "impl test 3 failed for n=2";

  // Test 4: n=5
  p := SpecialPermutation(5);
  e := BuildExpected(5);
  expect p == e, "impl test 4 failed for n=5";

  // Test 5: n=2,3,4
  p := SpecialPermutation(2);
  e := BuildExpected(2);
  expect p == e, "impl test 5 failed for n=2";
  p := SpecialPermutation(3);
  e := BuildExpected(3);
  expect p == e, "impl test 5 failed for n=3";
  p := SpecialPermutation(4);
  e := BuildExpected(4);
  expect p == e, "impl test 5 failed for n=4";

  // Test 6: n=10
  p := SpecialPermutation(10);
  e := BuildExpected(10);
  expect p == e, "impl test 6 failed for n=10";

  // Test 7: n=2,3,4,5,6
  p := SpecialPermutation(2);
  e := BuildExpected(2);
  expect p == e, "impl test 7 failed for n=2";
  p := SpecialPermutation(3);
  e := BuildExpected(3);
  expect p == e, "impl test 7 failed for n=3";
  p := SpecialPermutation(4);
  e := BuildExpected(4);
  expect p == e, "impl test 7 failed for n=4";
  p := SpecialPermutation(5);
  e := BuildExpected(5);
  expect p == e, "impl test 7 failed for n=5";
  p := SpecialPermutation(6);
  e := BuildExpected(6);
  expect p == e, "impl test 7 failed for n=6";

  // Test 8: n=7
  p := SpecialPermutation(7);
  e := BuildExpected(7);
  expect p == e, "impl test 8 failed for n=7";

  // Test 9: n=2, n=2
  p := SpecialPermutation(2);
  e := BuildExpected(2);
  expect p == e, "impl test 9 failed for n=2 (first)";
  p := SpecialPermutation(2);
  e := BuildExpected(2);
  expect p == e, "impl test 9 failed for n=2 (second)";

  // Test 10: n=50
  p := SpecialPermutation(50);
  e := BuildExpected(50);
  expect p == e, "impl test 10 failed for n=50";

  // Test 11: n=3,5,2,8
  p := SpecialPermutation(3);
  e := BuildExpected(3);
  expect p == e, "impl test 11 failed for n=3";
  p := SpecialPermutation(5);
  e := BuildExpected(5);
  expect p == e, "impl test 11 failed for n=5";
  p := SpecialPermutation(2);
  e := BuildExpected(2);
  expect p == e, "impl test 11 failed for n=2";
  p := SpecialPermutation(8);
  e := BuildExpected(8);
  expect p == e, "impl test 11 failed for n=8";

  // Test 12: n=3
  p := SpecialPermutation(3);
  e := BuildExpected(3);
  expect p == e, "impl test 12 failed for n=3";

  print "All tests passed\n";
}