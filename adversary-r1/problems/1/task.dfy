/*
 * Problem 1: Matrix Row-wise Prefix Sums
 *
 * Given a seq<seq<int>> representing a matrix, compute the row-wise
 * prefix sums. Each row in the output has the same length as the
 * corresponding input row, and output[i][j] = sum of input[i][0..j+1].
 *
 * The spec involves nested quantifiers over both dimensions and
 * requires relating each output element to a partial sum of the input row.
 */

// Sum of elements in a sequence from index 'lo' to 'hi' (exclusive)
function SumRange(s: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |s|
  decreases hi - lo
{
  if lo == hi then 0
  else s[lo] + SumRange(s, lo + 1, hi)
}

// The specification predicate for the prefix sum computation
ghost predicate PrefixSumSpec(input: seq<seq<int>>, output: seq<seq<int>>)
{
  // Same number of rows
  |output| == |input| &&
  // Each row has the same length
  (forall i :: 0 <= i < |input| ==> |output[i]| == |input[i]|) &&
  // Each element is the prefix sum
  (forall i, j :: 0 <= i < |input| && 0 <= j < |input[i]| ==>
    output[i][j] == SumRange(input[i], 0, j + 1))
}

// Compute row-wise prefix sums of a matrix
method PrefixSumMatrix(input: seq<seq<int>>) returns (output: seq<seq<int>>)
  ensures PrefixSumSpec(input, output)
{
  output := [];
  var i := 0;
  while i < |input|
    // INVARIANT NEEDED HERE
  {
    var row := input[i];
    var prefixRow: seq<int> := [];
    var j := 0;
    var runningSum := 0;
    while j < |row|
      // INVARIANT NEEDED HERE
    {
      runningSum := runningSum + row[j];
      prefixRow := prefixRow + [runningSum];
      j := j + 1;
    }
    output := output + [prefixRow];
    i := i + 1;
  }
}
