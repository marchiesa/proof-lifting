// Palindrome Check -- Test cases

predicate IsPalindromeSpec(a: seq<int>)
{
  forall i :: 0 <= i < |a| ==> a[i] == a[|a| - 1 - i]
}

method {:axiom} IsPalindrome(a: seq<int>) returns (result: bool)
  ensures result == IsPalindromeSpec(a)

method TestPalindrome()
{
  var a := [1, 2, 3, 2, 1];
  var r := IsPalindrome(a);
  assert a[0] == a[4] == 1;
  assert a[1] == a[3] == 2;
  assert a[2] == 3;
  assert IsPalindromeSpec(a);
  assert r;
}

method TestNotPalindrome()
{
  var a := [1, 2, 3];
  var r := IsPalindrome(a);
  assert a[0] == 1;
  assert a[2] == 3;
  assert a[0] != a[2];
  assert !IsPalindromeSpec(a);
  assert !r;
}

method TestEmpty()
{
  var a: seq<int> := [];
  var r := IsPalindrome(a);
  assert IsPalindromeSpec(a);
  assert r;
}

method TestSingleElement()
{
  var a := [42];
  var r := IsPalindrome(a);
  assert a[0] == a[0];
  assert IsPalindromeSpec(a);
  assert r;
}
