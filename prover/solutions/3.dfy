function countChar(s: seq<char>, c: char): int
{
  if |s| == 0 then 0
  else (if s[0] == c then 1 else 0) + countChar(s[1..], c)
}

lemma countCharAppend(s: seq<char>, x: char, c: char)
  ensures countChar(s + [x], c) == countChar(s, c) + (if x == c then 1 else 0)
{
  if |s| == 0 {
    assert s + [x] == [x];
  } else {
    var t := s + [x];
    assert t[0] == s[0];
    assert t[1..] == s[1..] + [x];
    countCharAppend(s[1..], x, c);
  }
}

method countOccurrences(s: seq<char>, c: char) returns (count: int)
  ensures count == countChar(s, c)
{
  count := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == countChar(s[..i], c)
  {
    assert s[..i+1] == s[..i] + [s[i]];
    countCharAppend(s[..i], s[i], c);
    if s[i] == c {
      count := count + 1;
    }
    i := i + 1;
  }
  assert s[..i] == s;
}
