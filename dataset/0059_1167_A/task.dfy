// --- Formal specification predicates ---

ghost predicate IsDigit(c: char)
{
  '0' <= c <= '9'
}

// A telephone number is exactly 11 digits where the first digit is '8'.
ghost predicate IsPhoneNumber(t: seq<char>)
{
  |t| == 11 && t[0] == '8' && (forall i | 0 <= i < |t| :: IsDigit(t[i]))
}

// `sub` can be obtained from `s` by deleting zero or more characters (preserving order).
ghost predicate IsSubsequence(sub: seq<char>, s: seq<char>)
  decreases |s|
{
  if |sub| == 0 then true
  else if |s| == 0 then false
  else
    // Either match sub[0] with s[0] and advance both, or skip s[0]
    (sub[0] == s[0] && IsSubsequence(sub[1..], s[1..]))
    || IsSubsequence(sub, s[1..])
}

// Compilable equivalent of: exists t :: IsPhoneNumber(t) && IsSubsequence(t, s).
// Enumerates all ways to select `remaining` characters from s in order;
// the first selected character must be '8', and every selected character must be a digit.
ghost predicate CanFormPhone(s: seq<char>, remaining: nat)
  decreases |s|
{
  if remaining == 0 then true
  else if |s| == 0 then false
  else
    // Skip s[0]
    CanFormPhone(s[1..], remaining)
    ||
    // Select s[0] as the next phone-number digit
    (IsDigit(s[0]) && (remaining == 11 ==> s[0] == '8') && CanFormPhone(s[1..], remaining - 1))
}

// --- Method with specification ---

method TelephoneNumber(s: string, n: int) returns (result: bool)
  requires n == |s|
  requires forall i | 0 <= i < n :: IsDigit(s[i])
  ensures result == CanFormPhone(s, 11)
{
  var i := 0;
  while i < n - 10
  {
    if s[i] == '8' {
      return true;
    }
    i := i + 1;
  }
  return false;
}