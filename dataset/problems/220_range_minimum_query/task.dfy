// Range Minimum Query
// Task: Add loop invariants so that Dafny can verify this program.

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
