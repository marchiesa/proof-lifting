// Range Minimum Query -- Reference solution with invariants

function Min(a: int, b: int): int { if a <= b then a else b }

function RangeMin(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo < hi <= |a|
  decreases hi - lo
{
  if hi - lo == 1 then a[lo]
  else Min(a[lo], RangeMin(a, lo + 1, hi))
}

lemma RangeMinExtend(a: seq<int>, lo: int, hi: int)
  requires 0 <= lo < hi < |a|
  ensures RangeMin(a, lo, hi + 1) == Min(RangeMin(a, lo, hi), a[hi])
  decreases hi - lo
{
  if hi - lo == 1 {
    assert RangeMin(a, lo, hi) == a[lo];
    assert RangeMin(a, lo, hi + 1) == Min(a[lo], RangeMin(a, lo + 1, hi + 1));
    assert RangeMin(a, lo + 1, hi + 1) == a[hi];
  } else {
    RangeMinExtend(a, lo + 1, hi);
    assert RangeMin(a, lo, hi + 1) == Min(a[lo], RangeMin(a, lo + 1, hi + 1));
    assert RangeMin(a, lo + 1, hi + 1) == Min(RangeMin(a, lo + 1, hi), a[hi]);
    assert RangeMin(a, lo, hi) == Min(a[lo], RangeMin(a, lo + 1, hi));
  }
}

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
    invariant 0 <= q <= |queryL|
    invariant |answers| == q
    invariant forall i :: 0 <= i < q ==> answers[i] == RangeMin(a, queryL[i], queryR[i])
    decreases |queryL| - q
  {
    var lo := queryL[q];
    var hi := queryR[q];
    var minVal := a[lo];
    var i := lo + 1;
    while i < hi
      invariant lo + 1 <= i <= hi
      invariant minVal == RangeMin(a, lo, i)
      decreases hi - i
    {
      RangeMinExtend(a, lo, i);
      minVal := Min(minVal, a[i]);
      i := i + 1;
    }
    answers := answers + [minVal];
    q := q + 1;
  }
}
