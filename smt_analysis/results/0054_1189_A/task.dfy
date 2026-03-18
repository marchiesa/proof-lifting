ghost function CountChar(s: string, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountChar(s[..|s|-1], c) + (if s[|s|-1] == c then 1 else 0)
}

ghost predicate IsGood(s: string)
{
  CountChar(s, '0') != CountChar(s, '1')
}

ghost predicate IsBinaryString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

ghost function Flatten(parts: seq<string>): string
  decreases |parts|
{
  if |parts| == 0 then ""
  else Flatten(parts[..|parts|-1]) + parts[|parts|-1]
}

ghost predicate AllGood(parts: seq<string>)
{
  forall i | 0 <= i < |parts| :: IsGood(parts[i])
}

method KeanuReeves(s: string) returns (k: int, parts: seq<string>)
  requires |s| > 0
  requires IsBinaryString(s)
  ensures k == |parts|
  ensures k == 1 || k == 2
  ensures Flatten(parts) == s
  ensures AllGood(parts)
  ensures k == 1 <==> IsGood(s)
{
  var zeros := 0;
  var ones := 0;
  var i := 0;
  while i < |s|
  {
    if s[i] == '0' {
      zeros := zeros + 1;
    } else {
      ones := ones + 1;
    }
    i := i + 1;
  }
  if zeros != ones {
    k := 1;
    parts := [s];
  } else {
    k := 2;
    parts := [s[..|s| - 1], [s[|s| - 1]]];
  }
}