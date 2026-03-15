// Binary Palindrome Check
// Task: Add loop invariants so that Dafny can verify this program.

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
