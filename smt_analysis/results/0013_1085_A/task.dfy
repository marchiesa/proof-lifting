// The Right-Left encryption: builds a string by writing s[0], then alternately
// appending (odd indices) and prepending (even indices >= 2) each subsequent character.
ghost function Encrypt(s: string): string
  decreases |s|
{
  if |s| == 0 then ""
  else if |s| == 1 then [s[0]]
  else if |s| % 2 == 0 then
    // Last character index is odd → append to the right
    Encrypt(s[..|s|-1]) + [s[|s|-1]]
  else
    // Last character index is even (>=2) → prepend to the left
    [s[|s|-1]] + Encrypt(s[..|s|-1])
}

// s is a valid decryption of ciphertext t iff encrypting s produces t
ghost predicate IsDecryptionOf(s: string, t: string)
{
  |s| == |t| && Encrypt(s) == t
}

method Decrypt(t: string) returns (s: string)
  ensures IsDecryptionOf(s, t)
{
  var n := |t|;
  if n == 0 {
    s := "";
    return;
  }
  var mid := (n - 1) / 2;
  s := [t[mid]];
  var u1: int := mid + 1;
  var u2: int := mid - 1;
  while u1 < n && u2 >= 0
  {
    s := s + [t[u1]];
    s := s + [t[u2]];
    u1 := u1 + 1;
    u2 := u2 - 1;
  }
  if n % 2 == 0 {
    s := s + [t[n - 1]];
  }
}