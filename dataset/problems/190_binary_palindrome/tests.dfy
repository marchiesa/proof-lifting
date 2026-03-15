// Binary Palindrome Check

predicate IsBinary(bits: seq<int>)
{
  forall i :: 0 <= i < |bits| ==> bits[i] == 0 || bits[i] == 1
}

predicate IsPalindrome(s: seq<int>)
{
  forall i :: 0 <= i < |s| ==> s[i] == s[|s| - 1 - i]
}

method BinaryPalindrome(bits: seq<int>) returns (result: bool)
  requires IsBinary(bits)
  ensures result == IsPalindrome(bits)
{
  if |bits| <= 1 {
    return true;
  }
  var lo := 0;
  var hi := |bits| - 1;
  while lo < hi
  {
    if bits[lo] != bits[hi] {
      return false;
    }
    lo := lo + 1;
    hi := hi - 1;
  }
  return true;
}

method Main()
{
  // Palindrome: [1,0,1]
  var a := [1, 0, 1];
  var r1 := BinaryPalindrome(a);
  expect r1 == true;
  expect IsPalindrome(a);

  // Not palindrome: [1,0,0]
  var b := [1, 0, 0];
  var r2 := BinaryPalindrome(b);
  expect r2 == false;
  expect !IsPalindrome(b);

  // Empty
  var c: seq<int> := [];
  var r3 := BinaryPalindrome(c);
  expect r3 == true;

  // Single element
  var d := [1];
  var r4 := BinaryPalindrome(d);
  expect r4 == true;

  // Even palindrome: [1,0,0,1]
  var e := [1, 0, 0, 1];
  var r5 := BinaryPalindrome(e);
  expect r5 == true;

  // Negative test
  var f := [0, 1, 1, 0, 1];
  expect !IsPalindrome(f);
  var r6 := BinaryPalindrome(f);
  expect r6 == false;

  print "All spec tests passed\n";
}
