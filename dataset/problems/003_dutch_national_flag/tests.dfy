// Dutch National Flag -- Runtime spec tests
// Note: The spec predicates (AllValidColors, IsSortedColors) use array reads,
// which can't be tested purely as predicates on sequences.
// We test ValidColor (the core predicate) and seq-based equivalents.

predicate ValidColor(c: int)
{
  c == 0 || c == 1 || c == 2
}

predicate AllValidColorsSeq(a: seq<int>)
{
  forall i | 0 <= i < |a| :: ValidColor(a[i])
}

predicate IsSortedColorsSeq(a: seq<int>)
{
  forall i, j | 0 <= i < j < |a| :: a[i] <= a[j]
}

method Main()
{
  // Test ValidColor
  expect ValidColor(0), "0 is a valid color";
  expect ValidColor(1), "1 is a valid color";
  expect ValidColor(2), "2 is a valid color";
  expect !ValidColor(3), "3 is not a valid color";
  expect !ValidColor(-1), "-1 is not a valid color";
  expect !ValidColor(10), "10 is not a valid color";

  // Test AllValidColorsSeq
  expect AllValidColorsSeq([0, 1, 2, 0, 1, 2]), "all 0,1,2 should be valid";
  expect AllValidColorsSeq([0, 0, 0]), "all zeros valid";
  expect AllValidColorsSeq([]), "empty should be valid";
  expect !AllValidColorsSeq([0, 1, 3]), "contains 3, not valid";
  expect !AllValidColorsSeq([0, -1, 2]), "contains -1, not valid";

  // Test IsSortedColorsSeq
  expect IsSortedColorsSeq([0, 0, 1, 1, 2, 2]), "sorted colors should be sorted";
  expect IsSortedColorsSeq([0, 1, 2]), "0,1,2 sorted";
  expect IsSortedColorsSeq([]), "empty sorted";
  expect IsSortedColorsSeq([1]), "single sorted";
  expect !IsSortedColorsSeq([2, 1, 0]), "reversed not sorted";
  expect !IsSortedColorsSeq([1, 0, 2]), "1,0,2 not sorted";
  expect IsSortedColorsSeq([0, 0, 0, 1, 2, 2]), "valid Dutch flag output";

  print "All spec tests passed\n";
}
