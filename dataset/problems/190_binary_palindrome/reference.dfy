// Binary Palindrome Check -- Reference solution with invariants

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
    invariant 0 <= lo <= hi + 1 <= |bits|
    invariant lo + hi == |bits| - 1
    invariant forall i :: 0 <= i < lo ==> bits[i] == bits[|bits| - 1 - i]
    decreases hi - lo
  {
    if bits[lo] != bits[hi] {
      return false;
    }
    lo := lo + 1;
    hi := hi - 1;
  }
  return true;
}
