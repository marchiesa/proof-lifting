// ---------------------------------------------------------------------------
// Specification predicates and functions
// ---------------------------------------------------------------------------

predicate IsSorted(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] <= s[j]
}

predicate PairwiseDistinct(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] != s[j]
}

predicate IsPermutation(a: seq<int>, b: seq<int>)
{
  multiset(a) == multiset(b)
}

function Sums(x: seq<int>, y: seq<int>): seq<int>
  requires |x| == |y|
  decreases |x|
{
  if |x| == 0 then []
  else Sums(x[..|x|-1], y[..|y|-1]) + [x[|x|-1] + y[|y|-1]]
}

// ---------------------------------------------------------------------------
// Combined spec predicate (checks all ensures of KuroniAndTheGifts)
// ---------------------------------------------------------------------------

predicate KuroniSpecOk(a: seq<int>, b: seq<int>, x: seq<int>, y: seq<int>)
  requires |a| == |b|
  requires |x| == |a|
  requires |y| == |a|
{
  IsPermutation(x, a) && IsPermutation(y, b) && PairwiseDistinct(Sums(x, y))
}

// ---------------------------------------------------------------------------
// Methods with specification
// ---------------------------------------------------------------------------

method Insert(sorted: seq<int>, val: int) returns (result: seq<int>)
  requires IsSorted(sorted)
  ensures IsSorted(result)
  ensures IsPermutation(result, sorted + [val])
{
  var i := 0;
  while i < |sorted| && sorted[i] < val
  {
    i := i + 1;
  }
  result := sorted[..i] + [val] + sorted[i..];
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures IsSorted(sorted)
  ensures IsPermutation(sorted, s)
{
  sorted := [];
  var i := 0;
  while i < |s|
  {
    sorted := Insert(sorted, s[i]);
    i := i + 1;
  }
}

method KuroniAndTheGifts(a: seq<int>, b: seq<int>) returns (x: seq<int>, y: seq<int>)
  requires |a| == |b|
  requires PairwiseDistinct(a)
  requires PairwiseDistinct(b)
  ensures |x| == |a|
  ensures |y| == |a|
  ensures IsPermutation(x, a)
  ensures IsPermutation(y, b)
  ensures PairwiseDistinct(Sums(x, y))
{
  x := SortSeq(a);
  y := SortSeq(b);
}

method Main()
{
  // =========================================================================
  // SPEC POSITIVE tests (small inputs, n <= 3)
  // =========================================================================

  // From Test 2: a=[5], b=[3] -> x=[5], y=[3]
  expect KuroniSpecOk([5], [3], [5], [3]), "spec positive 1";

  // From Test 3: a=[1,2], b=[3,4] -> x=[1,2], y=[3,4]
  expect KuroniSpecOk([1,2], [3,4], [1,2], [3,4]), "spec positive 2";

  // From Test 6.1: a=[1], b=[1] -> x=[1], y=[1]
  expect KuroniSpecOk([1], [1], [1], [1]), "spec positive 3";

  // From Test 6.2: a=[3,7], b=[5,2] -> x=[3,7], y=[2,5]
  expect KuroniSpecOk([3,7], [5,2], [3,7], [2,5]), "spec positive 4";

  // From Test 8.1: a=[42], b=[17] -> x=[42], y=[17]
  expect KuroniSpecOk([42], [17], [42], [17]), "spec positive 5";

  // From Test 8.2: a=[1,3], b=[2,4] -> x=[1,3], y=[2,4]
  expect KuroniSpecOk([1,3], [2,4], [1,3], [2,4]), "spec positive 6";

  // From Test 8.3: a=[5,10,15], b=[1,2,3] -> x=[5,10,15], y=[1,2,3]
  expect KuroniSpecOk([5,10,15], [1,2,3], [5,10,15], [1,2,3]), "spec positive 7";

  // From Test 1.1: a=[1,8,5], b=[8,4,5] -> x=[1,5,8], y=[4,5,8]
  expect KuroniSpecOk([1,8,5], [8,4,5], [1,5,8], [4,5,8]), "spec positive 8";

  // From Test 1.2: a=[1,7,5], b=[6,1,2] -> x=[1,5,7], y=[1,2,6]
  expect KuroniSpecOk([1,7,5], [6,1,2], [1,5,7], [1,2,6]), "spec positive 9";

  // =========================================================================
  // SPEC NEGATIVE tests (small inputs, n <= 3)
  // =========================================================================

  // From Neg 2: a=[5], b=[3], wrong x=[6], y=[3]
  expect !KuroniSpecOk([5], [3], [6], [3]), "spec negative 1";

  // From Neg 3: a=[1,2], b=[3,4], wrong x=[2,2], y=[3,4]
  expect !KuroniSpecOk([1,2], [3,4], [2,2], [3,4]), "spec negative 2";

  // From Neg 6: a=[1], b=[1], wrong x=[2], y=[1]
  expect !KuroniSpecOk([1], [1], [2], [1]), "spec negative 3";

  // From Neg 8: a=[42], b=[17], wrong x=[43], y=[17]
  expect !KuroniSpecOk([42], [17], [43], [17]), "spec negative 4";

  // From Neg 1: a=[1,8,5], b=[8,4,5], wrong x=[2,5,8], y=[4,5,8]
  expect !KuroniSpecOk([1,8,5], [8,4,5], [2,5,8], [4,5,8]), "spec negative 5";

  // From Neg 4: a=[1,7,5], b=[6,1,2], wrong x=[2,5,7], y=[1,2,6]
  expect !KuroniSpecOk([1,7,5], [6,1,2], [2,5,7], [1,2,6]), "spec negative 6";

  // =========================================================================
  // IMPLEMENTATION tests (full-size test pairs)
  // =========================================================================

  // Test 1, Case 1
  var x1, y1 := KuroniAndTheGifts([1, 8, 5], [8, 4, 5]);
  expect x1 == [1, 5, 8], "impl test 1 x failed";
  expect y1 == [4, 5, 8], "impl test 1 y failed";

  // Test 1, Case 2
  var x2, y2 := KuroniAndTheGifts([1, 7, 5], [6, 1, 2]);
  expect x2 == [1, 5, 7], "impl test 2 x failed";
  expect y2 == [1, 2, 6], "impl test 2 y failed";

  // Test 2
  var x3, y3 := KuroniAndTheGifts([5], [3]);
  expect x3 == [5], "impl test 3 x failed";
  expect y3 == [3], "impl test 3 y failed";

  // Test 3
  var x4, y4 := KuroniAndTheGifts([1, 2], [3, 4]);
  expect x4 == [1, 2], "impl test 4 x failed";
  expect y4 == [3, 4], "impl test 4 y failed";

  // Test 4
  var x5, y5 := KuroniAndTheGifts([1, 7, 5], [6, 1, 2]);
  expect x5 == [1, 5, 7], "impl test 5 x failed";
  expect y5 == [1, 2, 6], "impl test 5 y failed";

  // Test 5
  var x6, y6 := KuroniAndTheGifts([1, 2, 3, 4, 5], [10, 20, 30, 40, 50]);
  expect x6 == [1, 2, 3, 4, 5], "impl test 6 x failed";
  expect y6 == [10, 20, 30, 40, 50], "impl test 6 y failed";

  // Test 6, Case 1
  var x7, y7 := KuroniAndTheGifts([1], [1]);
  expect x7 == [1], "impl test 7 x failed";
  expect y7 == [1], "impl test 7 y failed";

  // Test 6, Case 2
  var x8, y8 := KuroniAndTheGifts([3, 7], [5, 2]);
  expect x8 == [3, 7], "impl test 8 x failed";
  expect y8 == [2, 5], "impl test 8 y failed";

  // Test 7
  var x9, y9 := KuroniAndTheGifts([10, 20, 30, 40], [1, 2, 3, 4]);
  expect x9 == [10, 20, 30, 40], "impl test 9 x failed";
  expect y9 == [1, 2, 3, 4], "impl test 9 y failed";

  // Test 8, Case 1
  var x10, y10 := KuroniAndTheGifts([42], [17]);
  expect x10 == [42], "impl test 10 x failed";
  expect y10 == [17], "impl test 10 y failed";

  // Test 8, Case 2
  var x11, y11 := KuroniAndTheGifts([1, 3], [2, 4]);
  expect x11 == [1, 3], "impl test 11 x failed";
  expect y11 == [2, 4], "impl test 11 y failed";

  // Test 8, Case 3
  var x12, y12 := KuroniAndTheGifts([5, 10, 15], [1, 2, 3]);
  expect x12 == [5, 10, 15], "impl test 12 x failed";
  expect y12 == [1, 2, 3], "impl test 12 y failed";

  // Test 9
  var x13, y13 := KuroniAndTheGifts([1, 2, 3, 4, 5, 6, 7, 8, 9, 10], [11, 12, 13, 14, 15, 16, 17, 18, 19, 20]);
  expect x13 == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10], "impl test 13 x failed";
  expect y13 == [11, 12, 13, 14, 15, 16, 17, 18, 19, 20], "impl test 13 y failed";

  // Test 10
  var x14, y14 := KuroniAndTheGifts([3, 1, 4, 1, 5, 9], [2, 7, 1, 8, 2, 8]);
  expect x14 == [1, 1, 3, 4, 5, 9], "impl test 14 x failed";
  expect y14 == [1, 2, 2, 7, 8, 8], "impl test 14 y failed";

  // Test 11, Case 1
  var x15, y15 := KuroniAndTheGifts([50, 40, 30, 20, 10], [5, 15, 25, 35, 45]);
  expect x15 == [10, 20, 30, 40, 50], "impl test 15 x failed";
  expect y15 == [5, 15, 25, 35, 45], "impl test 15 y failed";

  // Test 11, Case 2
  var x16, y16 := KuroniAndTheGifts([7, 3, 9, 1], [2, 8, 4, 6]);
  expect x16 == [1, 3, 7, 9], "impl test 16 x failed";
  expect y16 == [2, 4, 6, 8], "impl test 16 y failed";

  print "All tests passed\n";
}