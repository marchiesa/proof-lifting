method SpecialPermutation(n: int) returns (p: seq<int>)
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

  // Test 1: T=2, inputs: 2, 5
  p := SpecialPermutation(2);
  e := BuildExpected(2);
  expect p == e, "Test 1 failed for n=2";
  p := SpecialPermutation(5);
  e := BuildExpected(5);
  expect p == e, "Test 1 failed for n=5";

  // Test 2: T=100, inputs: 2..100 then 36
  var n := 2;
  while n <= 100 {
    p := SpecialPermutation(n);
    e := BuildExpected(n);
    expect p == e, "Test 2 failed";
    n := n + 1;
  }
  p := SpecialPermutation(36);
  e := BuildExpected(36);
  expect p == e, "Test 2 failed for n=36";

  // Test 3: T=1, input: 2
  p := SpecialPermutation(2);
  e := BuildExpected(2);
  expect p == e, "Test 3 failed for n=2";

  // Test 4: T=1, input: 5
  p := SpecialPermutation(5);
  e := BuildExpected(5);
  expect p == e, "Test 4 failed for n=5";

  // Test 5: T=3, inputs: 2, 3, 4
  p := SpecialPermutation(2);
  e := BuildExpected(2);
  expect p == e, "Test 5 failed for n=2";
  p := SpecialPermutation(3);
  e := BuildExpected(3);
  expect p == e, "Test 5 failed for n=3";
  p := SpecialPermutation(4);
  e := BuildExpected(4);
  expect p == e, "Test 5 failed for n=4";

  // Test 6: T=1, input: 10
  p := SpecialPermutation(10);
  e := BuildExpected(10);
  expect p == e, "Test 6 failed for n=10";

  // Test 7: T=5, inputs: 2, 3, 4, 5, 6
  p := SpecialPermutation(2);
  e := BuildExpected(2);
  expect p == e, "Test 7 failed for n=2";
  p := SpecialPermutation(3);
  e := BuildExpected(3);
  expect p == e, "Test 7 failed for n=3";
  p := SpecialPermutation(4);
  e := BuildExpected(4);
  expect p == e, "Test 7 failed for n=4";
  p := SpecialPermutation(5);
  e := BuildExpected(5);
  expect p == e, "Test 7 failed for n=5";
  p := SpecialPermutation(6);
  e := BuildExpected(6);
  expect p == e, "Test 7 failed for n=6";

  // Test 8: T=1, input: 7
  p := SpecialPermutation(7);
  e := BuildExpected(7);
  expect p == e, "Test 8 failed for n=7";

  // Test 9: T=2, inputs: 2, 2
  p := SpecialPermutation(2);
  e := BuildExpected(2);
  expect p == e, "Test 9 failed for n=2 (first)";
  p := SpecialPermutation(2);
  e := BuildExpected(2);
  expect p == e, "Test 9 failed for n=2 (second)";

  // Test 10: T=1, input: 50
  p := SpecialPermutation(50);
  e := BuildExpected(50);
  expect p == e, "Test 10 failed for n=50";

  // Test 11: T=4, inputs: 3, 5, 2, 8
  p := SpecialPermutation(3);
  e := BuildExpected(3);
  expect p == e, "Test 11 failed for n=3";
  p := SpecialPermutation(5);
  e := BuildExpected(5);
  expect p == e, "Test 11 failed for n=5";
  p := SpecialPermutation(2);
  e := BuildExpected(2);
  expect p == e, "Test 11 failed for n=2";
  p := SpecialPermutation(8);
  e := BuildExpected(8);
  expect p == e, "Test 11 failed for n=8";

  // Test 12: T=1, input: 3
  p := SpecialPermutation(3);
  e := BuildExpected(3);
  expect p == e, "Test 12 failed for n=3";

  print "All tests passed\n";
}