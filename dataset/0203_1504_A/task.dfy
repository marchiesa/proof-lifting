ghost predicate IsPalindrome(t: string)
{
  forall i | 0 <= i < |t| / 2 :: t[i] == t[|t| - 1 - i]
}

ghost function InsertCharAt(s: string, pos: nat): string
  requires pos <= |s|
{
  s[..pos] + "a" + s[pos..]
}

method DejaVu(s: string) returns (possible: bool, result: string)
  ensures possible ==>
    (exists pos | 0 <= pos <= |s| :: result == InsertCharAt(s, pos))
    && !IsPalindrome(result)
  ensures !possible ==>
    forall pos | 0 <= pos <= |s| :: IsPalindrome(InsertCharAt(s, pos))
{
  // Check if all characters are 'a'
  var allA := true;
  var i := 0;
  while i < |s| && allA {
    if s[i] != 'a' {
      allA := false;
    }
    i := i + 1;
  }

  if allA {
    possible := false;
    result := "";
    return;
  }

  // Check if s + "a" is a palindrome
  var sa := s + "a";
  var isPalin := true;
  var j := 0;
  while j < |sa| / 2 && isPalin {
    if sa[j] != sa[|sa| - 1 - j] {
      isPalin := false;
    }
    j := j + 1;
  }

  if isPalin {
    possible := true;
    result := "a" + s;
  } else {
    possible := true;
    result := s + "a";
  }
}