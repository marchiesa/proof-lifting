// Check Balanced Parentheses (Single Type) -- Reference solution with invariants

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

method CheckBalanced(s: seq<int>) returns (result: bool)
  requires forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1
  ensures result == IsBalanced(s)
{
  var depth := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant depth == Balance(s, i)
    invariant depth >= 0
    invariant forall k :: 0 <= k <= i ==> Balance(s, k) >= 0
    decreases |s| - i
  {
    if s[i] == 0 {
      depth := depth + 1;
    } else {
      depth := depth - 1;
    }
    if depth < 0 {
      assert Balance(s, i + 1) < 0;
      return false;
    }
    i := i + 1;
  }
  result := depth == 0;
}
