ghost function ToLower(c: char): char
{
  if 'A' <= c <= 'Z' then
    ((c as int - 'A' as int + 'a' as int) as char)
  else
    c
}

ghost predicate CIEqual(s: seq<char>, t: seq<char>)
{
  |s| == |t| &&
  forall i | 0 <= i < |s| :: ToLower(s[i]) == ToLower(t[i])
}

ghost predicate CILessThan(s: seq<char>, t: seq<char>)
{
  exists k | 0 <= k <= |s| && k <= |t| ::
    (forall j | 0 <= j < k :: ToLower(s[j]) == ToLower(t[j]))
    && ((k == |s| && k < |t|) || (k < |s| && k < |t| && ToLower(s[k]) < ToLower(t[k])))
}

method PetyaAndStrings(s: seq<char>, t: seq<char>) returns (result: int)
  ensures result == 0 <==> CIEqual(s, t)
  ensures result == -1 <==> CILessThan(s, t)
  ensures result == 1 <==> CILessThan(t, s)
{
  var len := if |s| < |t| then |s| else |t|;
  var i := 0;
  while i < len
  {
    var cs := s[i];
    var ct := t[i];
    if 'A' <= cs <= 'Z' {
      cs := (cs as int - 'A' as int + 'a' as int) as char;
    }
    if 'A' <= ct <= 'Z' {
      ct := (ct as int - 'A' as int + 'a' as int) as char;
    }
    if cs < ct {
      result := -1;
      return;
    } else if cs > ct {
      result := 1;
      return;
    }
    i := i + 1;
  }
  if |s| < |t| {
    result := -1;
  } else if |s| > |t| {
    result := 1;
  } else {
    result := 0;
  }
}