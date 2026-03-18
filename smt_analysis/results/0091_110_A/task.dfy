// --- Specification ---

ghost function Abs(n: int): nat {
  if n < 0 then -n else n
}

ghost predicate IsLuckyDigit(d: int) {
  d == 4 || d == 7
}

// Decimal digits of a positive number (most-significant first); 0 maps to [].
ghost function Digits(n: nat): seq<int>
  decreases n
{
  if n == 0 then []
  else Digits(n / 10) + [n % 10]
}

// Count of lucky digits in a sequence (slice-based recursion).
ghost function CountLucky(s: seq<int>): nat
  decreases |s|
{
  if |s| == 0 then 0
  else CountLucky(s[..|s|-1]) + (if IsLuckyDigit(s[|s|-1]) then 1 else 0)
}

// A lucky number is a positive integer whose every digit is 4 or 7.
ghost predicate IsLuckyNumber(n: nat) {
  var d := Digits(n);
  n > 0 && forall i :: 0 <= i < |d| ==> IsLuckyDigit(d[i])
}

// A number is nearly lucky iff the count of lucky digits in its
// decimal representation is itself a lucky number.
ghost predicate IsNearlyLucky(n: int) {
  IsLuckyNumber(CountLucky(Digits(Abs(n))))
}

// --- Implementation (body unchanged) ---

method NearlyLucky(n: int) returns (result: bool)
  ensures result == IsNearlyLucky(n)
{
  var num := if n < 0 then -n else n;
  if num == 0 {
    result := false;
    return;
  }
  var count := 0;
  var temp := num;
  while temp > 0 {
    var digit := temp % 10;
    if digit == 4 || digit == 7 {
      count := count + 1;
    }
    temp := temp / 10;
  }
  if count == 0 {
    result := false;
    return;
  }
  var flag := true;
  temp := count;
  while temp > 0 {
    var digit := temp % 10;
    if digit != 4 && digit != 7 {
      flag := false;
    }
    temp := temp / 10;
  }
  result := flag;
}