ghost predicate IsBinaryChar(c: char)
{
  c == '0' || c == '1'
}

ghost predicate IsBinaryString(s: string)
{
  forall i | 0 <= i < |s| :: IsBinaryChar(s[i])
}

ghost predicate Similar(a: string, b: string)
{
  |a| == |b| && exists i | 0 <= i < |a| :: a[i] == b[i]
}

method StringSimilarity(n: int, s: string) returns (w: string)
  requires n >= 1
  requires |s| == 2 * n - 1
  requires IsBinaryString(s)
  ensures |w| == n
  ensures IsBinaryString(w)
  ensures forall j | 0 <= j < n :: Similar(w, s[j..j + n])
{
  var c := s[n - 1];
  w := "";
  var i := 0;
  while i < n
  {
    w := w + [c];
    i := i + 1;
  }
}