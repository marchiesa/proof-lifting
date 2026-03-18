ghost function TriNum(k: nat): nat
{
  k * (k + 1) / 2
}

ghost function Repeat(c: char, count: nat): string
  decreases count
{
  if count == 0 then ""
  else [c] + Repeat(c, count - 1)
}

// Encryption per the problem: write s[0] once, s[1] twice, ..., s[m-1] m times
ghost function Encrypt(s: string): string
  decreases |s|
{
  if |s| == 0 then ""
  else Encrypt(s[..|s|-1]) + Repeat(s[|s|-1], |s|)
}

// t is a valid encryption: its length is triangular and each group is uniform
ghost predicate IsValidEncryption(t: string)
{
  exists m: nat ::
    TriNum(m) == |t| &&
    forall i | 0 <= i < m ::
      forall j | TriNum(i) <= j < TriNum(i + 1) ::
        t[j] == t[TriNum(i)]
}

method DecryptRepeatingCipher(t: string, n: int) returns (s: string)
  requires n == |t|
  requires IsValidEncryption(t)
  ensures Encrypt(s) == t
{
  s := "";
  var x := 0;
  var y := 1;
  while x < n && x < |t|
  {
    s := s + [t[x]];
    x := x + y;
    y := y + 1;
  }
}