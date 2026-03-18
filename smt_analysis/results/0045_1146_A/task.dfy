// Count the number of 'a' characters in a string
ghost function CountA(s: string): nat
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[|s|-1] == 'a' then 1 else 0) + CountA(s[..|s|-1])
}

// Can we form a "good" subsequence of exactly `len` characters from `s`?
// A good string has strictly more than half its characters equal to 'a'.
// We choose numA of the available 'a's and (len - numA) of the available non-'a's,
// such that 2 * numA > len (the "good" condition).
ghost predicate CanFormGoodOfLength(s: string, len: int)
{
  0 <= len <= |s| &&
  exists numA: int | 0 <= numA <= len ::
    numA <= CountA(s) &&
    len - numA + CountA(s) <= |s| &&
    2 * numA > len
}

method LoveA(s: string) returns (result: int)
  requires CountA(s) >= 1
  ensures 0 <= result <= |s|
  ensures CanFormGoodOfLength(s, result)
  ensures forall k | result < k <= |s| :: !CanFormGoodOfLength(s, k)
{
  var count := 0;
  var i := 0;
  while i < |s|
  {
    if s[i] == 'a' {
      count := count + 1;
    }
    i := i + 1;
  }
  var candidate := 2 * count - 1;
  if |s| < candidate {
    result := |s|;
  } else {
    result := candidate;
  }
}