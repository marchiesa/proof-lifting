// Specification: a dragon numbered i suffers damage if it is targeted by any
// of the four attacks (every k-th, l-th, m-th, or n-th dragon).
ghost predicate Suffers(i: int, k: int, l: int, m: int, n: int)
  requires k > 0 && l > 0 && m > 0 && n > 0
{
  i % k == 0 || i % l == 0 || i % m == 0 || i % n == 0
}

// Count how many dragons from 1 to d suffered damage.
ghost function CountSuffered(k: int, l: int, m: int, n: int, d: int): int
  requires k > 0 && l > 0 && m > 0 && n > 0
  requires d >= 0
  decreases d
{
  if d == 0 then 0
  else CountSuffered(k, l, m, n, d - 1) + (if Suffers(d, k, l, m, n) then 1 else 0)
}

method InsomniaCure(k: int, l: int, m: int, n: int, d: int) returns (count: int)
  requires k > 0 && l > 0 && m > 0 && n > 0
  requires d >= 0
  ensures count == CountSuffered(k, l, m, n, d)
{
  count := 0;
  var i := 1;
  while i <= d
  {
    if i % k == 0 || i % l == 0 || i % m == 0 || i % n == 0 {
      count := count + 1;
    }
    i := i + 1;
  }
}