// Range Minimum Query

function Min(a: int, b: int): int { if a <= b then a else b }

function RangeMin(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo < hi <= |a|
  decreases hi - lo
{
  if hi - lo == 1 then a[lo]
  else Min(a[lo], RangeMin(a, lo + 1, hi))
}

// Simple O(n) per query approach
method AnswerQueries(a: seq<int>, queryL: seq<int>, queryR: seq<int>) returns (answers: seq<int>)
  requires |a| > 0
  requires |queryL| == |queryR|
  requires forall i :: 0 <= i < |queryL| ==> 0 <= queryL[i] < queryR[i] <= |a|
  ensures |answers| == |queryL|
  ensures forall i :: 0 <= i < |answers| ==> answers[i] == RangeMin(a, queryL[i], queryR[i])
{
  answers := [];
  var q := 0;
  while q < |queryL|
  {
    var lo := queryL[q];
    var hi := queryR[q];
    var minVal := a[lo];
    var i := lo + 1;
    while i < hi
    {
      minVal := Min(minVal, a[i]);
      i := i + 1;
    }
    answers := answers + [minVal];
    q := q + 1;
  }
}

method Main()
{
  var a := [2, 4, 1, 5, 3];
  // Query [0, 3) => min of [2,4,1] = 1
  // Query [1, 4) => min of [4,1,5] = 1
  // Query [3, 5) => min of [5,3] = 3
  var r := AnswerQueries(a, [0, 1, 3], [3, 4, 5]);
  expect |r| == 3;
  expect r[0] == RangeMin(a, 0, 3);
  expect RangeMin(a, 0, 3) == 1;
  expect r[0] == 1;
  expect r[1] == 1;
  expect r[2] == 3;

  // Single element query
  var r2 := AnswerQueries(a, [2], [3]);
  expect r2[0] == 1;

  // Whole array
  var r3 := AnswerQueries(a, [0], [5]);
  expect r3[0] == RangeMin(a, 0, 5);

  // Negative test: RangeMin [0,1) should be a[0], not a[1]
  expect RangeMin(a, 0, 1) == 2;
  expect RangeMin(a, 0, 1) != 4;

  print "All spec tests passed\n";
}
