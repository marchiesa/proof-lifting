predicate IsPhotogenicPair(u: int, v: int) {
  (u + v) % 2 == 0
}

function CountPhotogenicPairs(s: seq<int>): int
  decreases |s|
{
  if |s| <= 1 then 0
  else (if IsPhotogenicPair(s[0], s[1]) then 1 else 0) + CountPhotogenicPairs(s[1..])
}

predicate CanExceed(remaining: seq<int>, last: int, accumulated: int, target: int)
  decreases |remaining|
{
  if |remaining| == 0 then
    accumulated > target
  else
    exists i | 0 <= i < |remaining| ::
      CanExceed(
        remaining[..i] + remaining[i+1..],
        remaining[i],
        accumulated + (if IsPhotogenicPair(last, remaining[i]) then 1 else 0),
        target
      )
}

predicate CanExceedFromStart(a: seq<int>, target: int)
{
  if |a| <= 1 then
    0 > target
  else
    exists i | 0 <= i < |a| ::
      CanExceed(a[..i] + a[i+1..], a[i], 0, target)
}

predicate MeetsSpec(a: seq<int>, result: seq<int>) {
  multiset(result) == multiset(a) && !CanExceedFromStart(a, CountPhotogenicPairs(result))
}

method AverageHeight(a: seq<int>) returns (result: seq<int>)
  ensures multiset(result) == multiset(a)
  ensures !CanExceedFromStart(a, CountPhotogenicPairs(result))
{
  var odd: seq<int> := [];
  var even: seq<int> := [];
  var i := 0;
  while i < |a|
  {
    if a[i] % 2 != 0 {
      odd := odd + [a[i]];
    } else {
      even := even + [a[i]];
    }
    i := i + 1;
  }
  result := odd + even;
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // (small inputs, length 1-3, values 0-5)

  // From test 1a/3: [1,1,2] -> [1,1,2]
  expect MeetsSpec([1, 1, 2], [1, 1, 2]), "spec positive 1";

  // From test 1b/6: [1,1,1] -> [1,1,1]
  expect MeetsSpec([1, 1, 1], [1, 1, 1]), "spec positive 2";

  // From test 2: [1,2] -> [1,2]
  expect MeetsSpec([1, 2], [1, 2]), "spec positive 3";

  // From test 10a: [1,1] -> [1,1]
  expect MeetsSpec([1, 1], [1, 1]), "spec positive 4";

  // From test 10c: [3,3,3] -> [3,3,3]
  expect MeetsSpec([3, 3, 3], [3, 3, 3]), "spec positive 5";

  // From test 7 scaled: [1,2,3] -> [1,3,2]
  expect MeetsSpec([1, 2, 3], [1, 3, 2]), "spec positive 6";

  // From test 9b scaled: [2,2,3] -> [3,2,2]
  expect MeetsSpec([2, 2, 3], [3, 2, 2]), "spec positive 7";

  // From test 1d scaled: [2,1] -> [1,2]
  expect MeetsSpec([2, 1], [1, 2]), "spec positive 8";

  // From test 4 scaled: [2,4] -> [2,4]
  expect MeetsSpec([2, 4], [2, 4]), "spec positive 9";

  // From test 5 scaled: [1,3] -> [1,3]
  expect MeetsSpec([1, 3], [1, 3]), "spec positive 10";

  // === SPEC NEGATIVE TESTS ===
  // (small inputs, wrong outputs should fail spec)

  // From neg 1/3: input [1,1,2], wrong [2,1,2]
  expect !MeetsSpec([1, 1, 2], [2, 1, 2]), "spec negative 1";

  // From neg 2: input [1,2], wrong [2,2]
  expect !MeetsSpec([1, 2], [2, 2]), "spec negative 2";

  // From neg 6: input [1,1,1], wrong [2,1,1]
  expect !MeetsSpec([1, 1, 1], [2, 1, 1]), "spec negative 3";

  // From neg 10: input [1,1], wrong [2,1]
  expect !MeetsSpec([1, 1], [2, 1]), "spec negative 4";

  // From neg 4 scaled: input [2,4], wrong [3,4]
  expect !MeetsSpec([2, 4], [3, 4]), "spec negative 5";

  // From neg 5 scaled: input [1,3], wrong [2,3]
  expect !MeetsSpec([1, 3], [2, 3]), "spec negative 6";

  // From neg 7 scaled: input [1,2,3], wrong [2,2,3]
  expect !MeetsSpec([1, 2, 3], [2, 2, 3]), "spec negative 7";

  // From neg 9 scaled: input [1,2,3], wrong [2,3,2]
  expect !MeetsSpec([1, 2, 3], [2, 3, 2]), "spec negative 8";

  // === IMPLEMENTATION TESTS ===
  var r: seq<int>;

  r := AverageHeight([1, 1, 2]);
  expect r == [1, 1, 2], "impl test 1a failed";

  r := AverageHeight([1, 1, 1]);
  expect r == [1, 1, 1], "impl test 1b failed";

  r := AverageHeight([10, 9, 13, 15, 3, 16, 9, 13]);
  expect r == [9, 13, 15, 3, 9, 13, 10, 16], "impl test 1c failed";

  r := AverageHeight([18, 9]);
  expect r == [9, 18], "impl test 1d failed";

  r := AverageHeight([1, 2]);
  expect r == [1, 2], "impl test 2 failed";

  r := AverageHeight([2, 4, 6, 8]);
  expect r == [2, 4, 6, 8], "impl test 4 failed";

  r := AverageHeight([1, 3, 5, 7, 9]);
  expect r == [1, 3, 5, 7, 9], "impl test 5 failed";

  r := AverageHeight([1, 2, 3, 4, 5, 6]);
  expect r == [1, 3, 5, 2, 4, 6], "impl test 7 failed";

  r := AverageHeight([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
  expect r == [1, 3, 5, 7, 9, 2, 4, 6, 8, 10], "impl test 8 failed";

  r := AverageHeight([5, 10, 15]);
  expect r == [5, 15, 10], "impl test 9a failed";

  r := AverageHeight([2, 2, 3, 3]);
  expect r == [3, 3, 2, 2], "impl test 9b failed";

  r := AverageHeight([1, 1]);
  expect r == [1, 1], "impl test 10a failed";

  r := AverageHeight([3, 3, 3]);
  expect r == [3, 3, 3], "impl test 10b failed";

  print "All tests passed\n";
}