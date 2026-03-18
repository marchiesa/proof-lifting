ghost predicate AllLowercase(s: string)
{
  forall i | 0 <= i < |s| :: 'a' <= s[i] <= 'z'
}

ghost predicate AllDistinct(s: string)
{
  forall i, j | 0 <= i < |s| && 0 <= j < |s| && i != j :: s[i] != s[j]
}

ghost function MinCharVal(s: string): int
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0] as int
  else
    var rest := MinCharVal(s[..|s|-1]);
    var last := s[|s|-1] as int;
    if last < rest then last else rest
}

ghost function MaxCharVal(s: string): int
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0] as int
  else
    var rest := MaxCharVal(s[..|s|-1]);
    var last := s[|s|-1] as int;
    if last > rest then last else rest
}

ghost predicate IsDiverse(s: string)
{
  AllLowercase(s) &&
  AllDistinct(s) &&
  (|s| == 0 || MaxCharVal(s) - MinCharVal(s) + 1 == |s|)
}

method DiverseStrings(strings: seq<string>) returns (results: seq<bool>)
  requires forall i | 0 <= i < |strings| :: AllLowercase(strings[i])
  ensures |results| == |strings|
  ensures forall i | 0 <= i < |strings| :: results[i] == IsDiverse(strings[i])
{
  results := [];
  var idx := 0;
  while idx < |strings|
  {
    var a := strings[idx];
    var b := new int[26];
    var j := 0;
    while j < 26
    {
      b[j] := 0;
      j := j + 1;
    }
    j := 0;
    while j < |a|
    {
      var c := a[j] as int - 97;
      if 0 <= c < 26 {
        b[c] := b[c] + 1;
      }
      j := j + 1;
    }
    var diverse := true;
    var y := 0;
    var x := 0;
    var k := 0;
    while k < 27
    {
      var val := if k < 26 then b[k] else 0;
      if val > 1 {
        diverse := false;
        break;
      }
      if y == 0 && val == 1 {
        y := 1;
      }
      if y == 1 && val == 0 {
        x := 1;
        y := 0;
      }
      if x == 1 && val >= 1 {
        diverse := false;
        break;
      }
      k := k + 1;
    }
    results := results + [diverse];
    idx := idx + 1;
  }
}