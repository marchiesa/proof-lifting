// Palindrome Check -- Runtime spec tests

predicate IsPalindromeSpec(a: seq<int>)
{
  forall i | 0 <= i < |a| :: a[i] == a[|a| - 1 - i]
}

method Main()
{
  // Positive cases - palindromes
  expect IsPalindromeSpec([1, 2, 3, 2, 1]), "odd-length palindrome";
  expect IsPalindromeSpec([1, 2, 2, 1]), "even-length palindrome";
  expect IsPalindromeSpec([42]), "single element is palindrome";
  expect IsPalindromeSpec([]), "empty is palindrome";
  expect IsPalindromeSpec([5, 5]), "two equal elements";
  expect IsPalindromeSpec([1, 2, 1]), "three-element palindrome";
  expect IsPalindromeSpec([7, 7, 7, 7]), "all same is palindrome";

  // Negative cases - not palindromes
  expect !IsPalindromeSpec([1, 2, 3]), "1,2,3 is not a palindrome";
  expect !IsPalindromeSpec([1, 2]), "1,2 is not a palindrome";
  expect !IsPalindromeSpec([1, 2, 3, 4, 5]), "ascending not palindrome";
  expect !IsPalindromeSpec([1, 2, 3, 2, 2]), "almost palindrome but not";
  expect !IsPalindromeSpec([1, 1, 2]), "1,1,2 is not a palindrome";

  print "All spec tests passed\n";
}
