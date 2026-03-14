/*
 * Problem 1: Matrix Row-wise Prefix Sums
 */

function SumRange(s: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |s|
  decreases hi - lo
{
  if lo == hi then 0
  else s[lo] + SumRange(s, lo + 1, hi)
}

ghost predicate PrefixSumSpec(input: seq<seq<int>>, output: seq<seq<int>>)
{
  |output| == |input| &&
  (forall i :: 0 <= i < |input| ==> |output[i]| == |input[i]|) &&
  (forall i, j :: 0 <= i < |input| && 0 <= j < |input[i]| ==>
    output[i][j] == SumRange(input[i], 0, j + 1))
}

lemma SumRangeAppend(s: seq<int>, lo: int, hi: int)
  requires 0 <= lo <= hi < |s|
  ensures SumRange(s, lo, hi + 1) == SumRange(s, lo, hi) + s[hi]
  decreases hi - lo
{
  if lo == hi {
    // SumRange(s, lo, lo+1) = s[lo] + SumRange(s, lo+1, lo+1) = s[lo] + 0 = s[lo]
    // SumRange(s, lo, lo) + s[lo] = 0 + s[lo] = s[lo]
  } else {
    // SumRange(s, lo, hi+1) = s[lo] + SumRange(s, lo+1, hi+1)
    // By induction: SumRange(s, lo+1, hi+1) = SumRange(s, lo+1, hi) + s[hi]
    SumRangeAppend(s, lo + 1, hi);
    // So SumRange(s, lo, hi+1) = s[lo] + SumRange(s, lo+1, hi) + s[hi]
    //                           = SumRange(s, lo, hi) + s[hi]
  }
}

method PrefixSumMatrix(input: seq<seq<int>>) returns (output: seq<seq<int>>)
  ensures PrefixSumSpec(input, output)
{
  output := [];
  var i := 0;
  while i < |input|
    invariant 0 <= i <= |input|
    invariant |output| == i
    invariant forall r :: 0 <= r < i ==> |output[r]| == |input[r]|
    invariant forall r, c :: 0 <= r < i && 0 <= c < |input[r]| ==>
      output[r][c] == SumRange(input[r], 0, c + 1)
  {
    var row := input[i];
    var prefixRow: seq<int> := [];
    var j := 0;
    var runningSum := 0;
    while j < |row|
      invariant 0 <= j <= |row|
      invariant |prefixRow| == j
      invariant runningSum == SumRange(row, 0, j)
      invariant forall c :: 0 <= c < j ==> prefixRow[c] == SumRange(row, 0, c + 1)
    {
      SumRangeAppend(row, 0, j);
      runningSum := runningSum + row[j];
      prefixRow := prefixRow + [runningSum];
      j := j + 1;
    }
    output := output + [prefixRow];
    i := i + 1;
  }
}
