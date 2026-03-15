// Longest Plateau -- Test cases

predicate PlateauAt(a: seq<int>, start: int, len: int)
  requires 0 <= start && len >= 1 && start + len <= |a|
{
  forall i :: start <= i < start + len ==> a[i] == a[start]
}

predicate HasPlateau(a: seq<int>, len: int)
  requires |a| > 0 && len >= 1
{
  exists s :: 0 <= s && s + len <= |a| && PlateauAt(a, s, len)
}

method Main()
{
  // Test PlateauAt - positive
  expect PlateauAt([1, 1, 1], 0, 3), "All same is plateau of 3";
  expect PlateauAt([1, 2, 2, 3], 1, 2), "Middle plateau of 2";

  // Test PlateauAt - negative
  expect !PlateauAt([1, 2, 3], 0, 3), "Different elements not a plateau";

  // Test HasPlateau
  expect HasPlateau([1, 1, 2, 2, 2, 3], 3), "Longest plateau is 3";
  expect HasPlateau([1, 1, 2, 2, 2, 3], 1), "Has plateau of 1";
  expect HasPlateau([1, 2, 3], 1), "Each element is plateau of 1";
  expect !HasPlateau([1, 2, 3], 2), "No plateau of 2 in [1,2,3]";

  // Test optimality
  expect HasPlateau([5, 5, 5, 5], 4), "All same: plateau of 4";
  expect !HasPlateau([5, 5, 5, 5], 5), "No plateau of 5 in len-4 seq";

  print "All spec tests passed\n";
}
