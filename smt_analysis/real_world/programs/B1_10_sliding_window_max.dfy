// Pattern: Compute maximum in a sliding window
// Source: monitoring systems, time-series analysis
// Real-world: network throughput monitoring, stock price analysis, sensor data

ghost function MaxOfSeq(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then s[0]
  else if s[|s|-1] > MaxOfSeq(s[..|s|-1]) then s[|s|-1]
  else MaxOfSeq(s[..|s|-1])
}

method MaxInRange(a: seq<int>, lo: int, hi: int) returns (m: int)
  requires 0 <= lo < hi <= |a|
  ensures m == MaxOfSeq(a[lo..hi])
  ensures forall i :: lo <= i < hi ==> a[i] <= m
  ensures exists i :: lo <= i < hi && a[i] == m
{
  m := a[lo];
  var i := lo + 1;
  while i < hi
    invariant lo + 1 <= i <= hi
    invariant m == MaxOfSeq(a[lo..i])
    invariant forall j :: lo <= j < i ==> a[j] <= m
    invariant exists j :: lo <= j < i && a[j] == m
  {
    assert a[lo..i+1] == a[lo..i] + [a[i]];  // SMT QUIRK: B1 sequence extensionality
    if a[i] > m {
      m := a[i];
    }
    i := i + 1;
  }
  assert a[lo..hi] == a[lo..hi];  // help close the loop
}
