// Palindrome Check -- Reference solution with invariants

predicate IsPalindromeSpec(a: seq<int>)
{
  forall i :: 0 <= i < |a| ==> a[i] == a[|a| - 1 - i]
}

method IsPalindrome(a: seq<int>) returns (result: bool)
  ensures result == IsPalindromeSpec(a)
{
  var i := 0;
  while i < |a| / 2
    invariant 0 <= i <= |a| / 2
    invariant forall j :: 0 <= j < i ==> a[j] == a[|a| - 1 - j]
    decreases |a| / 2 - i
  {
    if a[i] != a[|a| - 1 - i] {
      return false;
    }
    i := i + 1;
  }
  return true;
}
