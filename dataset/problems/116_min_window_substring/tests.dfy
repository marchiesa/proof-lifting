// Minimum Window Containing All Characters -- Runtime spec tests

// ContainsAll uses multiset which has bounded quantifier already
predicate ContainsAll(window: seq<int>, t: seq<int>)
{
  forall i :: 0 <= i < |t| ==> multiset(window)[t[i]] >= multiset(t)[t[i]]
}

// Bounded ContainsAll for runtime checking
function ContainsAllBounded(window: seq<int>, t: seq<int>, idx: int): bool
  requires 0 <= idx <= |t|
  decreases |t| - idx
{
  if idx == |t| then true
  else multiset(window)[t[idx]] >= multiset(t)[t[idx]] && ContainsAllBounded(window, t, idx + 1)
}

method Main()
{
  // ContainsAllBounded: positive cases
  expect ContainsAllBounded([1, 2, 3], [1, 2], 0), "[1,2,3] contains all of [1,2]";
  expect ContainsAllBounded([1, 2], [1, 2], 0), "[1,2] contains all of [1,2]";
  expect ContainsAllBounded([1, 1, 2], [1, 1], 0), "[1,1,2] contains all of [1,1]";
  expect ContainsAllBounded([1, 2, 3, 4, 5], [3], 0), "[1,2,3,4,5] contains [3]";

  // ContainsAllBounded: negative cases
  expect !ContainsAllBounded([1, 2], [3], 0), "[1,2] does not contain [3]";
  expect !ContainsAllBounded([1], [1, 1], 0), "[1] does not contain [1,1] (need two 1s)";
  expect !ContainsAllBounded([], [1], 0), "[] does not contain [1]";

  // ContainsAllBounded: empty target
  expect ContainsAllBounded([1, 2], [], 0), "Any window contains empty target";
  expect ContainsAllBounded([], [], 0), "Empty contains empty";

  // Test window property: window [1,2] contains all of [1,2]
  var s := [1, 2, 3, 1, 2];
  var t := [1, 2];
  expect ContainsAllBounded(s[0..2], t, 0), "Window s[0..2]=[1,2] contains [1,2]";
  expect ContainsAllBounded(s[3..5], t, 0), "Window s[3..5]=[1,2] contains [1,2]";
  expect !ContainsAllBounded(s[1..2], t, 0), "Window s[1..2]=[2] does not contain [1,2]";

  // Multiset count checks
  expect multiset([1, 2, 1])[1] == 2, "Count of 1 in [1,2,1] = 2";
  expect multiset([1, 2, 1])[2] == 1, "Count of 2 in [1,2,1] = 1";
  expect multiset([1, 2, 1])[3] == 0, "Count of 3 in [1,2,1] = 0";

  print "All spec tests passed\n";
}
