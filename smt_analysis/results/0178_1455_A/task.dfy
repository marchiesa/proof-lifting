// --- Specification: models the problem's operations directly ---

// Convert a digit sequence (most-significant first) to its numeric value
ghost function DigitsToNat(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0
  else DigitsToNat(s[..|s|-1]) * 10 + s[|s|-1]
}

// Convert a non-negative integer to its digit sequence
ghost function NatToDigits(n: int): seq<int>
  decreases n
{
  if n < 0 then [0]
  else if n < 10 then [n]
  else NatToDigits(n / 10) + [n % 10]
}

// Reverse a sequence
ghost function ReverseSeq(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else [s[|s|-1]] + ReverseSeq(s[..|s|-1])
}

// Strip leading zeros, keeping at least one digit
ghost function StripLeadingZeros(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| <= 1 then s
  else if s[0] == 0 then StripLeadingZeros(s[1..])
  else s
}

// f(x): write all digits of x backwards, then strip leading zeros
ghost function ReverseDigits(x: int): int
{
  if x < 0 then 0
  else
    var digits := NatToDigits(x);
    var reversed := ReverseSeq(digits);
    var stripped := StripLeadingZeros(reversed);
    DigitsToNat(stripped)
}

// g(x) = x / f(f(x))
ghost function GValue(x: int): int
{
  if x < 1 then 0
  else
    var ffx := ReverseDigits(ReverseDigits(x));
    if ffx == 0 then 0
    else x / ffx
}

// The number of distinct g(x) values for 1 <= x <= N
ghost function CountDistinctGValues(N: int): int
{
  if N < 1 then 0
  else |set x: int | 1 <= x <= N :: GValue(x)|
}

// A valid representation of a positive integer as a digit sequence
ghost predicate ValidPositiveDigitSeq(s: seq<int>)
{
  |s| > 0 &&
  s[0] != 0 &&
  (forall i | 0 <= i < |s| :: 0 <= s[i] <= 9)
}

// --- Working code with specification attached ---

method StrangeFunctions(n: seq<int>) returns (result: int)
  requires ValidPositiveDigitSeq(n)
  ensures result == CountDistinctGValues(DigitsToNat(n))
{
  result := |n|;
}

method Repeat(d: int, count: int) returns (s: seq<int>)
{
  s := [];
  var i := 0;
  while i < count {
    s := s + [d];
    i := i + 1;
  }
}

method StringToDigits(str: string) returns (s: seq<int>)
{
  s := [];
  var i := 0;
  while i < |str| {
    s := s + [str[i] as int - '0' as int];
    i := i + 1;
  }
}