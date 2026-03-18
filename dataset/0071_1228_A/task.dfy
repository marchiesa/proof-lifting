ghost function Digits(n: int): seq<int>
  requires n >= 0
  decreases n
{
  if n == 0 then []
  else Digits(n / 10) + [n % 10]
}

ghost predicate AllDistinct(s: seq<int>)
{
  forall i, j | 0 <= i < |s| && 0 <= j < |s| && i != j :: s[i] != s[j]
}

ghost predicate HasDistinctDigits(n: int)
  requires n >= 1
{
  AllDistinct(Digits(n))
}

method DistinctDigits(l: int, r: int) returns (x: int)
  requires l >= 1
  ensures x != -1 ==> l <= x <= r && HasDistinctDigits(x)
  ensures x == -1 ==> forall i | l <= i <= r :: !HasDistinctDigits(i)
{
  var i := l;
  while i <= r
  {
    var cnt := new int[10](_ => 0);
    var n := i;
    var ok := true;
    while n > 0
    {
      var d := n % 10;
      cnt[d] := cnt[d] + 1;
      if cnt[d] > 1 {
        ok := false;
      }
      n := n / 10;
    }
    if ok {
      return i;
    }
    i := i + 1;
  }
  return -1;
}