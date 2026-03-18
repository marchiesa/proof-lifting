predicate InRange(a: seq<int>)
{
  forall i | 0 <= i < |a| :: 1 <= a[i] <= 1000
}

predicate NoTripleSum(a: seq<int>)
{
  forall x, y, z | 0 <= x < |a| && 0 <= y < |a| && 0 <= z < |a| ::
    a[x] + a[y] != a[z]
}

predicate IsComplete(a: seq<int>)
{
  InRange(a) && NoTripleSum(a)
}

method Solve(n: int) returns (a: seq<int>)
  requires n >= 0
  ensures |a| == n
  ensures IsComplete(a)
{
  a := [];
  var i := 0;
  while i < n
  {
    a := a + [1];
    i := i + 1;
  }
}

method TestImplSolve(ns: seq<int>, testName: string)
  requires forall i | 0 <= i < |ns| :: ns[i] >= 0
{
  for i := 0 to |ns| {
    var r := Solve(ns[i]);
    expect |r| == ns[i], testName;
    for j := 0 to |r| {
      expect r[j] == 1, testName;
    }
  }
}

method Main()
{
  // =============================================
  // SPEC POSITIVE TESTS
  // Top-level ensures predicate: IsComplete(a)
  // Scaled down to small sizes (n^3 quantifier)
  // =============================================

  // From Test 13 (n=1, output=[1])
  expect IsComplete([1]), "spec positive 1";
  // From Test 7 (n=3, output=[1,1,1])
  expect IsComplete([1, 1, 1]), "spec positive 2";
  // From Test 1 (n=4, scaled to length 2)
  expect IsComplete([1, 1]), "spec positive 3";
  // From Test 7 (n=4, output=[1,1,1,1])
  expect IsComplete([1, 1, 1, 1]), "spec positive 4";
  // From Test 1 (n=5, output=[1,1,1,1,1])
  expect IsComplete([1, 1, 1, 1, 1]), "spec positive 5";
  // From Test 2 (n=1, output=[1]) — also verifying length ensures
  expect |[1]| == 1, "spec positive 6 length";
  // From Test 2 (n=2, scaled: output=[1,1]) — length ensures
  expect |[1, 1]| == 2, "spec positive 7 length";
  // From Test 2 (n=3, scaled: output=[1,1,1]) — length ensures
  expect |[1, 1, 1]| == 3, "spec positive 8 length";

  // =============================================
  // SPEC NEGATIVE TESTS
  // Top-level ensures predicate: IsComplete(a)
  // Wrong outputs have first element = 2
  // NoTripleSum fails: a[1]+a[1]=1+1=2=a[0]
  // =============================================

  // From Negative 7 (n=4, scaled to length 2: [2,1])
  expect !IsComplete([2, 1]), "spec negative 1";
  // From Negative 1 (n=5, scaled to length 3: [2,1,1])
  expect !IsComplete([2, 1, 1]), "spec negative 2";
  // From Negative 4 (n=31, scaled to length 4: [2,1,1,1])
  expect !IsComplete([2, 1, 1, 1]), "spec negative 3";
  // From Negative 5 (n=503, scaled to length 5: [2,1,1,1,1])
  expect !IsComplete([2, 1, 1, 1, 1]), "spec negative 4";
  // From Negative 6 (n=132, scaled to length 6: [2,1,1,1,1,1])
  expect !IsComplete([2, 1, 1, 1, 1, 1]), "spec negative 5";

  // =============================================
  // IMPLEMENTATION TESTS (full-size inputs)
  // =============================================

  // Test 1
  TestImplSolve([5, 4], "impl test 1");
  // Test 2
  TestImplSolve([20, 31, 23, 1, 2, 3, 6, 7, 8, 12, 14, 15, 26, 25, 37, 60, 81, 99, 101, 173, 256], "impl test 2");
  // Test 3
  TestImplSolve([1000], "impl test 3");
  // Test 4
  TestImplSolve([31, 23, 28, 26, 20, 25, 22, 29, 28, 21, 19, 27, 20, 41, 22, 23, 23, 21, 25, 26], "impl test 4");
  // Test 5
  TestImplSolve([503, 497], "impl test 5");
  // Test 6
  TestImplSolve([132, 131, 123, 112, 117, 129, 130, 126], "impl test 6");
  // Test 7
  TestImplSolve([4, 3], "impl test 7");
  // Test 8
  TestImplSolve([47, 46, 51, 59, 44, 52, 56, 51, 53, 47, 43, 50, 36, 61, 61, 42, 54, 52, 48, 47], "impl test 8");
  // Test 9
  TestImplSolve([45, 75, 52, 46, 44, 41, 52, 38, 57, 56, 42, 47, 44, 47, 59, 49, 42, 54, 54, 56], "impl test 9");
  // Test 10
  TestImplSolve([53, 46, 62, 50, 49, 44, 39, 56, 58, 48, 54, 50, 61, 47, 54, 45, 49, 44, 46, 45], "impl test 10");
  // Test 11
  TestImplSolve([48, 60, 57, 49, 45, 35, 49, 51, 48, 57, 38, 65, 50, 55, 49, 51, 45, 43, 64, 41], "impl test 11");
  // Test 12
  TestImplSolve([486, 514], "impl test 12");
  // Test 13
  TestImplSolve([1], "impl test 13");
  // Test 14
  TestImplSolve([8, 12, 9, 7, 11, 15, 8, 10, 10, 10], "impl test 14");
  // Test 15
  TestImplSolve([144, 154, 140, 148, 140, 138, 136], "impl test 15");
  // Test 16
  TestImplSolve([11, 8, 20, 12, 10, 17, 12, 15, 8, 10, 10, 14, 11, 8, 12, 17, 14, 18, 13, 12, 13, 11, 12, 18, 11, 11, 12, 14, 17, 11, 13, 14, 12, 11, 13, 12, 11, 15, 12, 12, 14, 15, 13, 7, 13, 13, 12, 16, 14, 9, 16, 13, 16, 9, 10, 19, 12, 12, 12, 14, 14, 8, 15, 16, 16, 11, 17, 9, 14, 11, 15, 15, 12, 11, 11, 19, 20], "impl test 16");
  // Test 17
  TestImplSolve([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44], "impl test 17");
  // Test 18
  TestImplSolve([45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62], "impl test 18");
  // Test 19
  TestImplSolve([63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76], "impl test 19");
  // Test 20
  TestImplSolve([77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88], "impl test 20");

  print "All tests passed\n";
}