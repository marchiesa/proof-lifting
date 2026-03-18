// --- Specification: models the problem's operations and definitions ---

function Ones(a: seq<int>): int
  ensures 0 <= Ones(a) <= |a|
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[|a|-1] == 1 then 1 else 0) + Ones(a[..|a|-1])
}

function Repeat(v: int, n: int): seq<int>
  requires n >= 0
  ensures |Repeat(v, n)| == n
  decreases n
{
  if n == 0 then [] else Repeat(v, n - 1) + [v]
}

predicate IsBinaryArray(a: seq<int>) {
  forall i | 0 <= i < |a| :: a[i] == 0 || a[i] == 1
}

predicate IsNonIncreasing(a: seq<int>) {
  forall i, j | 0 <= i < j < |a| :: a[i] >= a[j]
}

predicate ValidQueries(n: int, queries: seq<(int, int)>) {
  forall i | 0 <= i < |queries| ::
    (queries[i].0 == 1 || queries[i].0 == 2) &&
    (queries[i].0 == 1 ==> 1 <= queries[i].1 <= n) &&
    (queries[i].0 == 2 ==> 1 <= queries[i].1 <= n)
}

function ArrayState(init: seq<int>, queries: seq<(int, int)>): seq<int>
  requires ValidQueries(|init|, queries)
  ensures |ArrayState(init, queries)| == |init|
  decreases |queries|
{
  if |queries| == 0 then init
  else
    var prev := ArrayState(init, queries[..|queries|-1]);
    var q := queries[|queries|-1];
    if q.0 == 1 then prev[q.1 - 1 := 1 - prev[q.1 - 1]]
    else prev
}

function SortDescending(a: seq<int>): seq<int>
  ensures |SortDescending(a)| == |a|
{
  Repeat(1, Ones(a)) + Repeat(0, |a| - Ones(a))
}

function ExpectedResults(init: seq<int>, queries: seq<(int, int)>): seq<int>
  requires ValidQueries(|init|, queries)
  decreases |queries|
{
  if |queries| == 0 then []
  else
    var prev := ExpectedResults(init, queries[..|queries|-1]);
    var arr := ArrayState(init, queries[..|queries|-1]);
    var q := queries[|queries|-1];
    if q.0 == 2 then
      var sorted := SortDescending(arr);
      prev + [sorted[q.1 - 1]]
    else
      prev
}

// --- Method with specification ---

method KthLargestValue(a: seq<int>, queries: seq<(int, int)>) returns (results: seq<int>)
  requires IsBinaryArray(a)
  requires ValidQueries(|a|, queries)
  ensures results == ExpectedResults(a, queries)
{
  var arr := a;
  var s := 0;
  var i := 0;
  while i < |arr| {
    s := s + arr[i];
    i := i + 1;
  }

  results := [];
  i := 0;
  while i < |queries| {
    var t := queries[i].0;
    var x := queries[i].1;
    if t == 1 {
      s := s - arr[x - 1];
      arr := arr[x - 1 := 1 - arr[x - 1]];
      s := s + arr[x - 1];
    } else {
      if x <= s {
        results := results + [1];
      } else {
        results := results + [0];
      }
    }
    i := i + 1;
  }
}

method Main()
{
  // =============================================
  // (a) SPEC POSITIVE tests (small inputs, testing ExpectedResults directly)
  // =============================================

  // Spec positive 1 (from Test 2): a=[0], queries=[(2,1)], expected=[0]
  expect ExpectedResults([0], [(2,1)]) == [0], "spec positive 1";

  // Spec positive 2 (from Test 7): a=[0], queries=[(1,1),(2,1),(1,1)], expected=[1]
  expect ExpectedResults([0], [(1,1),(2,1),(1,1)]) == [1], "spec positive 2";

  // Spec positive 3 (from Test 5): a=[0,0], queries=[(2,1),(1,1),(2,1),(1,1),(2,2)], expected=[0,1,0]
  expect ExpectedResults([0,0], [(2,1),(1,1),(2,1),(1,1),(2,2)]) == [0,1,0], "spec positive 3";

  // Spec positive 4 (from Test 3): a=[0,1,0], queries=[(2,1),(1,2),(2,2),(2,3)], expected=[1,0,0]
  expect ExpectedResults([0,1,0], [(2,1),(1,2),(2,2),(2,3)]) == [1,0,0], "spec positive 4";

  // Spec positive 5 (from Test 10): a=[1,1,1], queries=[(2,1),(1,1),(2,1),(1,2),(2,2),(2,3)], expected=[1,1,0,0]
  expect ExpectedResults([1,1,1], [(2,1),(1,1),(2,1),(1,2),(2,2),(2,3)]) == [1,1,0,0], "spec positive 5";

  // =============================================
  // (b) SPEC NEGATIVE tests (small inputs, testing ExpectedResults with wrong output)
  // =============================================

  // Spec negative 1 (from Neg 2): a=[0], queries=[(2,1)], wrong=[1]
  expect ExpectedResults([0], [(2,1)]) != [1], "spec negative 1";

  // Spec negative 2 (from Neg 7): a=[0], queries=[(1,1),(2,1),(1,1)], wrong=[2]
  expect ExpectedResults([0], [(1,1),(2,1),(1,1)]) != [2], "spec negative 2";

  // Spec negative 3 (from Neg 5): a=[0,0], queries=[(2,1),(1,1),(2,1),(1,1),(2,2)], wrong=[1,1,0]
  expect ExpectedResults([0,0], [(2,1),(1,1),(2,1),(1,1),(2,2)]) != [1,1,0], "spec negative 3";

  // Spec negative 4 (from Neg 3): a=[0,1,0], queries=[(2,1),(1,2),(2,2),(2,3)], wrong=[2,0,0]
  expect ExpectedResults([0,1,0], [(2,1),(1,2),(2,2),(2,3)]) != [2,0,0], "spec negative 4";

  // Spec negative 5 (from Neg 10): a=[1,1,1], queries=[(2,1),(1,1),(2,1),(1,2),(2,2),(2,3)], wrong=[2,1,0,0]
  expect ExpectedResults([1,1,1], [(2,1),(1,1),(2,1),(1,2),(2,2),(2,3)]) != [2,1,0,0], "spec negative 5";

  // =============================================
  // (c) IMPLEMENTATION tests (full-size test pairs)
  // =============================================

  // Impl test 1
  var r1 := KthLargestValue([1, 1, 0, 1, 0], [(2,3), (1,2), (2,3), (2,1), (2,5)]);
  expect r1 == [1, 0, 1, 0], "impl test 1 failed";

  // Impl test 2
  var r2 := KthLargestValue([0], [(2,1)]);
  expect r2 == [0], "impl test 2 failed";

  // Impl test 3
  var r3 := KthLargestValue([0, 1, 0], [(2,1), (1,2), (2,2), (2,3)]);
  expect r3 == [1, 0, 0], "impl test 3 failed";

  // Impl test 4
  var r4 := KthLargestValue([1, 1, 1, 1], [(2,1), (2,4), (1,3)]);
  expect r4 == [1, 1], "impl test 4 failed";

  // Impl test 5
  var r5 := KthLargestValue([0, 0], [(2,1), (1,1), (2,1), (1,1), (2,2)]);
  expect r5 == [0, 1, 0], "impl test 5 failed";

  // Impl test 6
  var r6 := KthLargestValue([1, 0, 1, 0, 1], [(2,2), (1,4), (2,2), (1,5), (2,3), (2,5)]);
  expect r6 == [1, 1, 1, 0], "impl test 6 failed";

  // Impl test 7
  var r7 := KthLargestValue([0], [(1,1), (2,1), (1,1)]);
  expect r7 == [1], "impl test 7 failed";

  // Impl test 8
  var r8 := KthLargestValue([0, 0, 0, 0, 0, 0], [(2,6), (1,3), (2,1), (2,6)]);
  expect r8 == [0, 1, 0], "impl test 8 failed";

  // Impl test 9
  var r9 := KthLargestValue([1, 0, 1, 1, 0, 0, 1], [(2,4), (1,7), (1,2), (2,1), (2,7)]);
  expect r9 == [1, 1, 0], "impl test 9 failed";

  // Impl test 10
  var r10 := KthLargestValue([1, 1, 1], [(2,1), (1,1), (2,1), (1,2), (2,2), (2,3)]);
  expect r10 == [1, 1, 0, 0], "impl test 10 failed";

  // Impl test 11
  var r11 := KthLargestValue([0, 1, 0, 1, 0, 1, 0, 1], [(2,4), (1,3), (2,4), (1,6), (2,5), (1,1), (2,8)]);
  expect r11 == [1, 1, 0, 0], "impl test 11 failed";

  // Impl test 12
  var r12 := KthLargestValue([1, 0, 0, 1, 1, 0, 1, 0, 0, 1], [(2,5), (1,10), (2,1), (1,4), (2,6), (1,7), (2,10), (2,3)]);
  expect r12 == [1, 1, 0, 0, 0], "impl test 12 failed";

  // =============================================
  // (d) All tests passed
  // =============================================
  print "All tests passed\n";
}