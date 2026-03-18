ghost predicate IsDigitChar(c: char)
{
  '0' <= c <= '9'
}

ghost predicate AllDigits(s: string)
{
  forall i | 0 <= i < |s| :: IsDigitChar(s[i])
}

ghost function DigitVal(c: char): int
  requires IsDigitChar(c)
{
  (c as int) - ('0' as int)
}

// The natural number represented by a non-empty digit string
ghost function StringToNat(s: string): int
  requires |s| > 0
  requires AllDigits(s)
  decreases |s|
{
  if |s| == 1 then DigitVal(s[0])
  else StringToNat(s[..|s|-1]) * 10 + DigitVal(s[|s|-1])
}

// Count how many substrings ending at the last position of s are even.
// Candidates: s[0..|s|], s[1..|s|], ..., s[|s|-1..|s|]
ghost function CountEvenEndingHere(s: string): int
  requires |s| > 0
  requires AllDigits(s)
  decreases |s|
{
  var thisOne := if StringToNat(s) % 2 == 0 then 1 else 0;
  if |s| == 1 then thisOne
  else thisOne + CountEvenEndingHere(s[1..])
}

// Total count of even substrings of s:
// |{ (l, r) | 0 <= l <= r < |s| && StringToNat(s[l..r+1]) % 2 == 0 }|
ghost function CountEvenSubstrings(s: string): int
  requires AllDigits(s)
  decreases |s|
{
  if |s| == 0 then 0
  else CountEvenSubstrings(s[..|s|-1]) + CountEvenEndingHere(s)
}

method EvenSubstrings(s: string) returns (count: int)
  requires AllDigits(s)
  ensures count == CountEvenSubstrings(s)
{
  count := 0;
  for i := 0 to |s| {
    if s[i] == '0' || s[i] == '2' || s[i] == '4' || s[i] == '6' || s[i] == '8' {
      count := count + i + 1;
    }
  }
}