ghost function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

ghost predicate IsGood(b: seq<int>)
{
  |b| > 0 && Sum(b) % |b| == 0
}

ghost predicate AllElementsInRange(a: seq<int>)
{
  forall i | 0 <= i < |a| :: 1 <= a[i] <= 100
}

ghost predicate AllSubarraysGood(a: seq<int>)
{
  forall i, j | 0 <= i < j <= |a| :: IsGood(a[i..j])
}

ghost predicate IsPerfect(a: seq<int>)
{
  |a| > 0 && AllElementsInRange(a) && AllSubarraysGood(a)
}

method PerfectArray(n: int) returns (a: seq<int>)
  requires n >= 1
  ensures |a| == n
  ensures IsPerfect(a)
{
  a := [];
  var i := 0;
  while i < n
  {
    a := a + [1];
    i := i + 1;
  }
}

method RepeatOne(n: int) returns (s: seq<int>)
{
  s := [];
  var i := 0;
  while i < n
  {
    s := s + [1];
    i := i + 1;
  }
}