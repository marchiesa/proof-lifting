ghost function CountOccurrences(a: seq<int>, v: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else CountOccurrences(a[..|a|-1], v) + (if a[|a|-1] == v then 1 else 0)
}

ghost predicate IsMajorityValue(a: seq<int>, v: int)
{
  CountOccurrences(a, v) == |a| - 1
}

ghost predicate IsSpyIndex(a: seq<int>, idx: int)
{
  1 <= idx <= |a| &&
  exists k | 0 <= k < |a| :: IsMajorityValue(a, a[k]) && a[idx - 1] != a[k]
}

method SpyDetected(a: seq<int>) returns (idx: int)
  requires |a| >= 3
  requires forall i | 0 <= i < |a| :: a[i] > 0
  requires exists k | 0 <= k < |a| :: IsMajorityValue(a, a[k])
  ensures IsSpyIndex(a, idx)
{
  var i := 0;
  while i < |a|
  {
    var count := 0;
    var j := 0;
    while j < |a|
    {
      if a[j] == a[i] {
        count := count + 1;
      }
      j := j + 1;
    }
    if count == 1 {
      return i + 1;
    }
    i := i + 1;
  }
  return 0;
}