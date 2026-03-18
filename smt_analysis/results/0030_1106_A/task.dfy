ghost predicate ValidMatrix(M: seq<seq<char>>, n: int)
{
  n >= 0 &&
  |M| == n &&
  (forall i | 0 <= i < n :: |M[i]| == n)
}

ghost predicate IsCrossAt(M: seq<seq<char>>, n: int, a: int, b: int)
  requires ValidMatrix(M, n)
  requires 0 <= a < n && 0 <= b < n
{
  1 <= a <= n - 2 &&
  1 <= b <= n - 2 &&
  M[a][b] == 'X' &&
  M[a-1][b-1] == 'X' &&
  M[a-1][b+1] == 'X' &&
  M[a+1][b-1] == 'X' &&
  M[a+1][b+1] == 'X'
}

ghost function CrossCount(M: seq<seq<char>>, n: int): int
  requires ValidMatrix(M, n)
{
  |set a, b | 0 <= a < n && 0 <= b < n && IsCrossAt(M, n, a, b) :: (a, b)|
}

method CountCrosses(n: int, M: seq<seq<char>>) returns (count: int)
  requires ValidMatrix(M, n)
  ensures count == CrossCount(M, n)
{
  count := 0;
  if n < 3 {
    return;
  }
  var a := 1;
  while a < n - 1
  {
    var b := 1;
    while b < n - 1
    {
      if M[a][b] == 'X'
         && M[a-1][b-1] == 'X'
         && M[a-1][b+1] == 'X'
         && M[a+1][b-1] == 'X'
         && M[a+1][b+1] == 'X'
      {
        count := count + 1;
      }
      b := b + 1;
    }
    a := a + 1;
  }
}