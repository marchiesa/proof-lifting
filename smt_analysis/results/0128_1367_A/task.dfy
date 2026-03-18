// Bob's encoding: concatenate all length-2 substrings of a, left to right.
// E.g., BobEncode("abac") == "ab" + "ba" + "ac" == "abbaac"
ghost function BobEncode(a: string): string
  requires |a| >= 2
  decreases |a|
{
  if |a| == 2 then a
  else a[0..2] + BobEncode(a[1..])
}

method ShortSubstrings(b: string) returns (a: string)
  requires |b| >= 2
  requires |b| % 2 == 0
  ensures |a| >= 2
  ensures BobEncode(a) == b
{
  a := "";
  var i := 1;
  while i < |b|
  {
    a := a + [b[i]];
    i := i + 2;
  }
  a := [b[0]] + a;
}