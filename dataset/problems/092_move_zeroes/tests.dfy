// Move Zeroes to End -- Runtime spec tests

function NonZeroes(a: seq<int>): seq<int>
{
  if |a| == 0 then []
  else if a[0] != 0 then [a[0]] + NonZeroes(a[1..])
  else NonZeroes(a[1..])
}

function CountZeroes(a: seq<int>): int
{
  if |a| == 0 then 0
  else (if a[0] == 0 then 1 else 0) + CountZeroes(a[1..])
}

method Main()
{
  // NonZeroes: positive cases
  expect NonZeroes([0, 1, 0, 3, 12]) == [1, 3, 12], "NonZeroes of [0,1,0,3,12] should be [1,3,12]";
  expect NonZeroes([1, 2, 3]) == [1, 2, 3], "NonZeroes of no-zero list should be same";
  expect NonZeroes([0, 0, 0]) == [], "NonZeroes of all-zero list should be empty";
  expect NonZeroes([]) == [], "NonZeroes of empty list should be empty";
  expect NonZeroes([5]) == [5], "NonZeroes of [5] should be [5]";
  expect NonZeroes([0]) == [], "NonZeroes of [0] should be []";

  // NonZeroes: negative cases
  expect NonZeroes([0, 1, 0, 3, 12]) != [1, 12, 3], "NonZeroes preserves order";
  expect NonZeroes([0, 1, 0, 3, 12]) != [0, 1, 3, 12], "NonZeroes should not include zeros";

  // CountZeroes: positive cases
  expect CountZeroes([0, 1, 0, 3, 12]) == 2, "CountZeroes of [0,1,0,3,12] should be 2";
  expect CountZeroes([1, 2, 3]) == 0, "CountZeroes of no-zero list should be 0";
  expect CountZeroes([0, 0, 0]) == 3, "CountZeroes of all-zero list should be 3";
  expect CountZeroes([]) == 0, "CountZeroes of empty should be 0";

  // CountZeroes: negative cases
  expect CountZeroes([0, 1, 0]) != 1, "CountZeroes of [0,1,0] should not be 1";
  expect CountZeroes([0, 1, 0]) != 3, "CountZeroes of [0,1,0] should not be 3";

  // Relationship: |NonZeroes| + CountZeroes == |a|
  var a := [0, 1, 0, 3, 12];
  expect |NonZeroes(a)| + CountZeroes(a) == |a|, "NonZeroes count + zero count == length";

  print "All spec tests passed\n";
}
