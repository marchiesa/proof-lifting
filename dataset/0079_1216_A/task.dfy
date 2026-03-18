ghost predicate ValidAB(s: seq<char>)
{
  forall i | 0 <= i < |s| :: s[i] == 'a' || s[i] == 'b'
}

ghost function CountChar(s: seq<char>, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountChar(s[..|s|-1], c) + (if s[|s|-1] == c then 1 else 0)
}

ghost predicate BalancedPrefixes(s: seq<char>)
{
  forall k | 1 <= k <= |s| / 2 :: CountChar(s[..2 * k], 'a') == CountChar(s[..2 * k], 'b')
}

ghost function HammingDist(s: seq<char>, t: seq<char>): int
  requires |s| == |t|
  decreases |s|
{
  if |s| == 0 then 0
  else HammingDist(s[..|s|-1], t[..|t|-1]) + (if s[|s|-1] != t[|s|-1] then 1 else 0)
}

// Counts consecutive pairs where both characters are the same.
// Each such pair requires at least one replacement to become balanced,
// and one replacement always suffices, so this equals the minimum ops.
ghost function CountBadPairs(s: seq<char>): int
  requires |s| % 2 == 0
  decreases |s|
{
  if |s| == 0 then 0
  else CountBadPairs(s[..|s|-2]) + (if s[|s|-2] == s[|s|-1] then 1 else 0)
}

method Prefixes(s: seq<char>) returns (ops: int, result: seq<char>)
  requires |s| % 2 == 0
  requires ValidAB(s)
  ensures |result| == |s|
  ensures ValidAB(result)
  ensures BalancedPrefixes(result)
  ensures ops == HammingDist(s, result)
  ensures ops == CountBadPairs(s)
{
  ops := 0;
  result := [];
  var i := 0;
  while i < |s|
  {
    if s[i] == s[i + 1] {
      result := result + ['a', 'b'];
      ops := ops + 1;
    } else {
      result := result + [s[i], s[i + 1]];
    }
    i := i + 2;
  }
}