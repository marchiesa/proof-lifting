// Check Balanced Parentheses (Single Type) -- Test cases

function Balance(s: seq<int>, k: int): int
  requires 0 <= k <= |s|
{
  if k == 0 then 0
  else Balance(s, k - 1) + (if s[k - 1] == 0 then 1 else -1)
}

predicate IsBalanced(s: seq<int>)
{
  (forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1) &&
  (forall k :: 0 <= k <= |s| ==> Balance(s, k) >= 0) &&
  Balance(s, |s|) == 0
}

method {:axiom} CheckBalanced(s: seq<int>) returns (result: bool)
  requires forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1
  ensures result == IsBalanced(s)

method TestBalanced()
{
  // 0 = '(', 1 = ')'
  // (()) = [0, 0, 1, 1]
  var r := CheckBalanced([0, 0, 1, 1]);
  assert Balance([0, 0, 1, 1], 0) == 0;
  assert Balance([0, 0, 1, 1], 1) == 1;
  assert Balance([0, 0, 1, 1], 2) == 2;
  assert Balance([0, 0, 1, 1], 3) == 1;
  assert Balance([0, 0, 1, 1], 4) == 0;
  assert r;
}

method TestUnbalanced()
{
  // )( = [1, 0]
  var r := CheckBalanced([1, 0]);
  assert Balance([1, 0], 1) == -1;
  assert !r;
}

method TestEmpty()
{
  var r := CheckBalanced([]);
  assert r;
}
