// Running Average (Partial Sums) -- Test cases

function Sum(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else s[0] + Sum(s[1..])
}

predicate IsPartialSums(a: seq<int>, result: seq<int>)
{
  |result| == |a| &&
  forall i :: 0 <= i < |a| ==> result[i] == Sum(a[..i+1])
}

method Main()
{
  // Test Sum
  expect Sum([]) == 0, "Sum of empty is 0";
  expect Sum([5]) == 5, "Sum of [5] is 5";
  expect Sum([1, 2, 3]) == 6, "Sum of [1,2,3] is 6";

  // Test IsPartialSums - positive
  expect IsPartialSums([], []), "Empty case";
  expect IsPartialSums([5], [5]), "Single element";
  expect IsPartialSums([1, 2, 3], [1, 3, 6]), "[1,2,3] -> [1,3,6]";
  expect IsPartialSums([3, -1, 4], [3, 2, 6]), "[3,-1,4] -> [3,2,6]";

  // Test IsPartialSums - negative
  expect !IsPartialSums([1, 2, 3], [1, 2, 3]), "Wrong partial sums";
  expect !IsPartialSums([1, 2], [1]), "Wrong length";
  expect !IsPartialSums([1, 2, 3], [1, 3, 5]), "Last element wrong";

  print "All spec tests passed\n";
}
