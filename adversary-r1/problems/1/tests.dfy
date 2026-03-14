/*
 * Tests for Problem 1: Matrix Row-wise Prefix Sums
 *
 * We test the spec predicate PrefixSumSpec on known input-output pairs.
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

// Helper lemma to unfold SumRange for small cases
lemma SumRangeUnfold1(s: seq<int>)
  requires |s| >= 1
  ensures SumRange(s, 0, 1) == s[0]
{
}

lemma SumRangeUnfold2(s: seq<int>)
  requires |s| >= 2
  ensures SumRange(s, 0, 2) == s[0] + s[1]
{
}

lemma SumRangeUnfold3(s: seq<int>)
  requires |s| >= 3
  ensures SumRange(s, 0, 3) == s[0] + s[1] + s[2]
{
}

// Test 1: Empty matrix
method test1()
{
  var input: seq<seq<int>> := [];
  var output: seq<seq<int>> := [];
  assert PrefixSumSpec(input, output);
}

// Test 2: Single row [1, 2, 3] -> [1, 3, 6]
method test2()
{
  var input := [[1, 2, 3]];
  var output := [[1, 3, 6]];

  var row := [1, 2, 3];
  SumRangeUnfold1(row);
  SumRangeUnfold2(row);
  SumRangeUnfold3(row);

  assert SumRange(row, 0, 1) == 1;
  assert SumRange(row, 0, 2) == 3;
  assert SumRange(row, 0, 3) == 6;

  // Now prove the spec
  assert input[0] == row;
  assert output[0][0] == SumRange(input[0], 0, 1);
  assert output[0][1] == SumRange(input[0], 0, 2);
  assert output[0][2] == SumRange(input[0], 0, 3);
  assert PrefixSumSpec(input, output);
}

// Test 3: Two rows [[1, 2], [3, 4, 5]] -> [[1, 3], [3, 7, 12]]
method test3()
{
  var input := [[1, 2], [3, 4, 5]];
  var output := [[1, 3], [3, 7, 12]];

  var row0 := [1, 2];
  var row1 := [3, 4, 5];

  SumRangeUnfold1(row0);
  SumRangeUnfold2(row0);
  SumRangeUnfold1(row1);
  SumRangeUnfold2(row1);
  SumRangeUnfold3(row1);

  assert input[0] == row0;
  assert input[1] == row1;

  assert output[0][0] == SumRange(input[0], 0, 1);
  assert output[0][1] == SumRange(input[0], 0, 2);
  assert output[1][0] == SumRange(input[1], 0, 1);
  assert output[1][1] == SumRange(input[1], 0, 2);
  assert output[1][2] == SumRange(input[1], 0, 3);

  assert PrefixSumSpec(input, output);
}

// Test 4: Row with negative numbers [5, -3, 2] -> [5, 2, 4]
method test4()
{
  var input := [[5, -3, 2]];
  var output := [[5, 2, 4]];

  var row := [5, -3, 2];
  SumRangeUnfold1(row);
  SumRangeUnfold2(row);
  SumRangeUnfold3(row);

  assert input[0] == row;
  assert output[0][0] == SumRange(input[0], 0, 1);
  assert output[0][1] == SumRange(input[0], 0, 2);
  assert output[0][2] == SumRange(input[0], 0, 3);
  assert PrefixSumSpec(input, output);
}
