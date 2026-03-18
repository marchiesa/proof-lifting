ghost predicate IsLuckyDigit(c: char)
{
  c == '4' || c == '7'
}

ghost predicate AllLuckyDigits(s: seq<char>)
{
  forall i | 0 <= i < |s| :: IsLuckyDigit(s[i])
}

ghost function DigitValue(c: char): int
{
  (c as int) - ('0' as int)
}

ghost function DigitSum(s: seq<char>): int
  decreases |s|
{
  if |s| == 0 then 0
  else DigitSum(s[..|s|-1]) + DigitValue(s[|s|-1])
}

ghost predicate IsLuckyTicket(s: seq<char>)
{
  var half := |s| / 2;
  AllLuckyDigits(s) && DigitSum(s[..half]) == DigitSum(s[half..])
}

method LuckyTicket(n: int, s: seq<char>) returns (result: bool)
  requires |s| == n
  requires n > 0
  requires n % 2 == 0
  ensures result == IsLuckyTicket(s)
{
  var a := 0;
  var b := 0;
  var half := |s| / 2;
  var i := 0;
  while i < |s|
  {
    if s[i] != '4' && s[i] != '7' {
      result := false;
      return;
    }
    var digit := (s[i] as int) - ('0' as int);
    if i < half {
      a := a + digit;
    } else {
      b := b + digit;
    }
    i := i + 1;
  }
  result := (a == b);
}