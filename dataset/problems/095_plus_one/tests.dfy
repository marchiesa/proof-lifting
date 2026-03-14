// Plus One -- Runtime spec tests

predicate ValidDigits(digits: seq<int>)
{
  forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
}

function PlusOneSpec(digits: seq<int>): seq<int>
  requires ValidDigits(digits)
  decreases |digits|
{
  if |digits| == 0 then [1]
  else if digits[|digits|-1] < 9 then
    digits[..|digits|-1] + [digits[|digits|-1] + 1]
  else
    PlusOneSpec(digits[..|digits|-1]) + [0]
}

method Main()
{
  // PlusOneSpec: no carry
  expect PlusOneSpec([1, 2, 3]) == [1, 2, 4], "PlusOne of [1,2,3] should be [1,2,4]";
  expect PlusOneSpec([0]) == [1], "PlusOne of [0] should be [1]";
  expect PlusOneSpec([1, 0, 0]) == [1, 0, 1], "PlusOne of [1,0,0] should be [1,0,1]";

  // PlusOneSpec: with carry
  expect PlusOneSpec([1, 2, 9]) == [1, 3, 0], "PlusOne of [1,2,9] should be [1,3,0]";
  expect PlusOneSpec([1, 9, 9]) == [2, 0, 0], "PlusOne of [1,9,9] should be [2,0,0]";

  // PlusOneSpec: all nines
  expect PlusOneSpec([9, 9, 9]) == [1, 0, 0, 0], "PlusOne of [9,9,9] should be [1,0,0,0]";
  expect PlusOneSpec([9]) == [1, 0], "PlusOne of [9] should be [1,0]";

  // PlusOneSpec: negative tests
  expect PlusOneSpec([1, 2, 3]) != [1, 2, 3], "PlusOne should change something";
  expect PlusOneSpec([9, 9, 9]) != [9, 9, 10], "PlusOne should carry properly";

  // PlusOneSpec: empty
  expect PlusOneSpec([]) == [1], "PlusOne of [] should be [1]";

  print "All spec tests passed\n";
}
