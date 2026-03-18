predicate ValidInput(n: int, a: seq<int>, b: seq<int>, c: seq<int>)
{
  n >= 3 &&
  |a| == n && |b| == n && |c| == n &&
  forall i | 0 <= i < n :: a[i] != b[i] && a[i] != c[i] && b[i] != c[i]
}

predicate ChosenFromOptions(p: seq<int>, a: seq<int>, b: seq<int>, c: seq<int>)
  requires |p| == |a| == |b| == |c|
{
  forall i | 0 <= i < |p| :: p[i] == a[i] || p[i] == b[i] || p[i] == c[i]
}

predicate NoAdjacentEqual(p: seq<int>)
  requires |p| >= 1
{
  (forall i | 0 <= i < |p| - 1 :: p[i] != p[i + 1]) &&
  p[|p| - 1] != p[0]
}

predicate ValidColoring(p: seq<int>, n: int, a: seq<int>, b: seq<int>, c: seq<int>)
{
  |p| == n && n >= 3 &&
  |a| == n && |b| == n && |c| == n &&
  ChosenFromOptions(p, a, b, c) &&
  NoAdjacentEqual(p)
}

method CircleColoring(n: int, a: seq<int>, b: seq<int>, c: seq<int>) returns (p: seq<int>)
  requires ValidInput(n, a, b, c)
  ensures ValidColoring(p, n, a, b, c)
{
  var out := new int[n];
  var i := 0;
  while i < n {
    out[i] := -1;
    i := i + 1;
  }
  i := 0;
  while i < n {
    var prev := (i - 1 + n) % n;
    var next := (i + 1) % n;
    if a[i] != out[prev] && a[i] != out[next] {
      out[i] := a[i];
    }
    if b[i] != out[prev] && b[i] != out[next] {
      out[i] := b[i];
    }
    if c[i] != out[prev] && c[i] != out[next] {
      out[i] := c[i];
    }
    i := i + 1;
  }
  p := out[..];
}

method Main()
{
  var p: seq<int>;

  // ===== SPEC POSITIVE TESTS =====
  // ValidColoring with correct outputs on small (n=3) inputs

  expect ValidColoring([3,2,1], 3, [1,1,1], [2,2,2], [3,3,3]), "spec positive 1";
  expect ValidColoring([3,1,2], 3, [1,2,1], [2,3,3], [3,1,2]), "spec positive 2";
  expect ValidColoring([3,1,2], 3, [1,2,3], [2,3,1], [3,1,2]), "spec positive 3";
  expect ValidColoring([30,10,20], 3, [10,20,30], [20,30,10], [30,10,20]), "spec positive 4";
  expect ValidColoring([7,5,6], 3, [5,6,7], [6,7,5], [7,5,6]), "spec positive 5";
  expect ValidColoring([3,2,1], 3, [1,1,2], [2,3,1], [3,2,3]), "spec positive 6";
  expect ValidColoring([2,3,1], 3, [1,2,3], [3,1,2], [2,3,1]), "spec positive 7";

  // ===== SPEC NEGATIVE TESTS =====
  // ValidColoring must reject wrong outputs

  // 4 not in {1,2,3} at position 0 -> ChosenFromOptions fails
  expect !ValidColoring([4,2,1], 3, [1,1,1], [2,2,2], [3,3,3]), "spec negative 1";
  // 4 not in {1,2,3} at position 0 -> ChosenFromOptions fails
  expect !ValidColoring([4,1,2], 3, [1,2,3], [2,3,1], [3,1,2]), "spec negative 2";
  // 4 not in {1,2,3} at position 0 -> ChosenFromOptions fails (n=4, still small)
  expect !ValidColoring([4,2,3,2], 4, [1,1,1,1], [2,2,2,2], [3,3,3,3]), "spec negative 3";
  // 31 not in {10,20,30} at position 0 -> ChosenFromOptions fails
  expect !ValidColoring([31,10,20], 3, [10,20,30], [20,30,10], [30,10,20]), "spec negative 5";
  // 4 not in {1,2,3} at position 0 -> ChosenFromOptions fails
  expect !ValidColoring([4,2,1], 3, [1,1,2], [2,3,1], [3,2,3]), "spec negative 8";
  // p[0]==p[1]==3 -> NoAdjacentEqual fails
  expect !ValidColoring([3,3,1], 3, [1,2,3], [3,1,2], [2,3,1]), "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====

  // Test 1, Case 1: n=3
  p := CircleColoring(3, [1,1,1], [2,2,2], [3,3,3]);
  expect p == [3,2,1], "impl test 1.1 failed";

  // Test 1, Case 2: n=4
  p := CircleColoring(4, [1,2,1,2], [2,1,2,1], [3,4,3,4]);
  expect p == [3,4,3,4], "impl test 1.2 failed";

  // Test 1, Case 3: n=7
  p := CircleColoring(7, [1,3,3,1,1,1,1], [2,4,4,3,2,2,4], [4,2,2,2,4,4,2]);
  expect p == [4,2,4,2,4,2,1], "impl test 1.3 failed";

  // Test 1, Case 4: n=3
  p := CircleColoring(3, [1,2,1], [2,3,3], [3,1,2]);
  expect p == [3,1,2], "impl test 1.4 failed";

  // Test 1, Case 5: n=10
  p := CircleColoring(10, [1,1,1,2,2,2,3,3,3,1], [2,2,2,3,3,3,1,1,1,2], [3,3,3,1,1,1,2,2,2,3]);
  expect p == [3,2,3,1,3,1,2,1,2,1], "impl test 1.5 failed";

  // Test 2: n=3
  p := CircleColoring(3, [1,2,3], [2,3,1], [3,1,2]);
  expect p == [3,1,2], "impl test 2 failed";

  // Test 3: n=4
  p := CircleColoring(4, [1,1,1,1], [2,2,2,2], [3,3,3,3]);
  expect p == [3,2,3,2], "impl test 3 failed";

  // Test 4: n=5
  p := CircleColoring(5, [1,2,3,4,5], [2,3,4,5,1], [3,4,5,1,2]);
  expect p == [3,4,5,1,2], "impl test 4 failed";

  // Test 5: n=3
  p := CircleColoring(3, [10,20,30], [20,30,10], [30,10,20]);
  expect p == [30,10,20], "impl test 5 failed";

  // Test 6, Case 1: n=3
  p := CircleColoring(3, [1,1,1], [2,2,2], [3,3,3]);
  expect p == [3,2,1], "impl test 6.1 failed";

  // Test 6, Case 2: n=3
  p := CircleColoring(3, [5,6,7], [6,7,5], [7,5,6]);
  expect p == [7,5,6], "impl test 6.2 failed";

  // Test 7: n=6
  p := CircleColoring(6, [1,1,2,2,3,3], [2,2,3,3,1,1], [3,3,1,1,2,2]);
  expect p == [3,2,1,3,2,1], "impl test 7 failed";

  // Test 8: n=3
  p := CircleColoring(3, [1,1,2], [2,3,1], [3,2,3]);
  expect p == [3,2,1], "impl test 8 failed";

  // Test 9: n=7
  p := CircleColoring(7, [1,2,1,2,1,2,1], [2,1,2,1,2,1,2], [3,3,3,3,3,3,3]);
  expect p == [3,1,3,1,3,1,2], "impl test 9 failed";

  // Test 10, Case 1: n=3
  p := CircleColoring(3, [1,2,3], [3,1,2], [2,3,1]);
  expect p == [2,3,1], "impl test 10.1 failed";

  // Test 10, Case 2: n=4
  p := CircleColoring(4, [5,5,5,5], [6,6,6,6], [7,7,7,7]);
  expect p == [7,6,7,6], "impl test 10.2 failed";

  // Test 10, Case 3: n=5
  p := CircleColoring(5, [1,3,5,7,9], [2,4,6,8,10], [3,5,7,9,11]);
  expect p == [3,5,7,9,11], "impl test 10.3 failed";

  // Test 11: n=10
  p := CircleColoring(10, [1,2,3,4,5,6,7,8,9,10], [2,3,4,5,6,7,8,9,10,1], [3,4,5,6,7,8,9,10,1,2]);
  expect p == [3,4,5,6,7,8,9,10,1,2], "impl test 11 failed";

  print "All tests passed\n";
}