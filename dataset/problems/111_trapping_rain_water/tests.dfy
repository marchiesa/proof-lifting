// Trapping Rain Water -- Runtime spec tests

function Max(a: int, b: int): int { if a >= b then a else b }
function Min(a: int, b: int): int { if a <= b then a else b }

function PrefixMax(a: seq<int>, n: int): int
  requires 0 < n <= |a|
  decreases n
{
  if n == 1 then a[0]
  else Max(PrefixMax(a, n - 1), a[n - 1])
}

function SuffixMax(a: seq<int>, n: int): int
  requires 0 <= n < |a|
  decreases |a| - n
{
  if n == |a| - 1 then a[n]
  else Max(a[n], SuffixMax(a, n + 1))
}

method Main()
{
  // PrefixMax tests
  var a := [0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1];
  expect PrefixMax(a, 1) == 0, "PrefixMax(a, 1) = 0";
  expect PrefixMax(a, 2) == 1, "PrefixMax(a, 2) = max(0,1) = 1";
  expect PrefixMax(a, 3) == 1, "PrefixMax(a, 3) = 1";
  expect PrefixMax(a, 4) == 2, "PrefixMax(a, 4) = 2";
  expect PrefixMax(a, 8) == 3, "PrefixMax(a, 8) = 3";

  // SuffixMax tests
  expect SuffixMax(a, 11) == 1, "SuffixMax at last element";
  expect SuffixMax(a, 10) == 2, "SuffixMax(a, 10) = max(2,1) = 2";
  expect SuffixMax(a, 7) == 3, "SuffixMax(a, 7) = 3";
  expect SuffixMax(a, 0) == 3, "SuffixMax(a, 0) = 3";

  // PrefixMax: negative tests
  expect PrefixMax(a, 4) != 1, "PrefixMax(a, 4) should be 2 not 1";

  // SuffixMax: negative tests
  expect SuffixMax(a, 10) != 1, "SuffixMax(a, 10) should be 2 not 1";

  // Simple cases
  expect PrefixMax([5, 3, 7], 1) == 5, "PrefixMax of [5,3,7] at 1 is 5";
  expect PrefixMax([5, 3, 7], 2) == 5, "PrefixMax of [5,3,7] at 2 is 5";
  expect PrefixMax([5, 3, 7], 3) == 7, "PrefixMax of [5,3,7] at 3 is 7";
  expect SuffixMax([5, 3, 7], 0) == 7, "SuffixMax of [5,3,7] at 0 is 7";
  expect SuffixMax([5, 3, 7], 1) == 7, "SuffixMax of [5,3,7] at 1 is 7";
  expect SuffixMax([5, 3, 7], 2) == 7, "SuffixMax of [5,3,7] at 2 is 7";

  // Water at position i = max(0, min(prefixMax[i-1], suffixMax[i+1]) - a[i])
  // For a = [0,1,0,2,...], at index 2: min(PrefixMax(a,2), SuffixMax(a,3)) - a[2]
  // = min(1, 3) - 0 = 1
  expect Min(PrefixMax(a, 2), SuffixMax(a, 3)) - a[2] == 1,
    "Water at index 2 should be 1";

  print "All spec tests passed\n";
}
