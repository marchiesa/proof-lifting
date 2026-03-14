// Check Balanced Parentheses (Single Type) -- Runtime spec tests

// 0 = '(', 1 = ')'
function Balance(s: seq<int>, k: int): int
  requires 0 <= k <= |s|
{
  if k == 0 then 0
  else Balance(s, k - 1) + (if s[k - 1] == 0 then 1 else -1)
}

predicate IsBalanced(s: seq<int>)
{
  (forall i | 0 <= i < |s| :: s[i] == 0 || s[i] == 1) &&
  (forall k | 0 <= k <= |s| :: Balance(s, k) >= 0) &&
  Balance(s, |s|) == 0
}

method Main() {
  // Balance function tests
  expect Balance([0, 0, 1, 1], 0) == 0, "balance at 0";
  expect Balance([0, 0, 1, 1], 1) == 1, "balance at 1";
  expect Balance([0, 0, 1, 1], 2) == 2, "balance at 2";
  expect Balance([0, 0, 1, 1], 3) == 1, "balance at 3";
  expect Balance([0, 0, 1, 1], 4) == 0, "balance at 4";

  // IsBalanced positive cases
  expect IsBalanced([]), "empty is balanced";
  expect IsBalanced([0, 1]), "() is balanced";
  expect IsBalanced([0, 0, 1, 1]), "(()) is balanced";
  expect IsBalanced([0, 1, 0, 1]), "()() is balanced";

  // IsBalanced negative cases
  expect !IsBalanced([1, 0]), ")( is not balanced";
  expect !IsBalanced([0, 0, 1]), "(() is not balanced";
  expect !IsBalanced([0, 1, 1]), "()) is not balanced";
  expect !IsBalanced([1]), "single ) is not balanced";
  expect !IsBalanced([0]), "single ( is not balanced";

  print "All spec tests passed\n";
}
