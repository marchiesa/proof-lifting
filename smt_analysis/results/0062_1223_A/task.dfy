// A correct match equation (CME) is a + b = c where a, b, c are all positive integers
ghost predicate IsValidCME(a: int, b: int, c: int)
{
  a >= 1 && b >= 1 && c >= 1 && a + b == c
}

// Can exactly `total` matches be used to form a valid CME?
// Each of a, b, c is represented by that many matches, so a + b + c == total.
// Since c = a + b, we have a + b = total/2 and we search over valid values of a.
ghost predicate CanFormCMEWithMatches(total: int)
{
  exists a | 1 <= a <= total / 2 - 1 ::
    var b := total / 2 - a;
    IsValidCME(a, b, a + b) && a + b + (a + b) == total
}

method CME(n: int) returns (extra: int)
  ensures extra >= 0
  ensures CanFormCMEWithMatches(n + extra)
  ensures forall e | 0 <= e < extra :: !CanFormCMEWithMatches(n + e)
{
  if n < 4 {
    extra := 4 - n;
  } else {
    extra := n % 2;
  }
}