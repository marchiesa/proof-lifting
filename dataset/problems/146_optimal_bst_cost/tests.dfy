// Optimal BST Cost -- Test cases

function SumFreq(freq: seq<int>, i: int, j: int): int
  requires 0 <= i <= j <= |freq|
  decreases j - i
{
  if i == j then 0
  else freq[i] + SumFreq(freq, i + 1, j)
}

method Main()
{
  expect SumFreq([10, 12, 20], 0, 3) == 42, "Sum of all freqs";
  expect SumFreq([10, 12, 20], 0, 1) == 10, "First freq";
  expect SumFreq([10, 12, 20], 1, 2) == 12, "Second freq";
  expect SumFreq([], 0, 0) == 0, "Empty sum";

  // Negative cases
  expect SumFreq([10, 12, 20], 0, 3) != 40, "Sum != 40";

  print "All spec tests passed\n";
}
