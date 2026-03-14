// Palindrome Check
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsPalindromeSpec(a: seq<int>)
{
  forall i :: 0 <= i < |a| ==> a[i] == a[|a| - 1 - i]
}

method IsPalindrome(a: seq<int>) returns (result: bool)
  ensures result == IsPalindromeSpec(a)
{
  var i := 0;
  while i < |a| / 2
  {
    if a[i] != a[|a| - 1 - i] {
      return false;
    }
    i := i + 1;
  }
  return true;
}
