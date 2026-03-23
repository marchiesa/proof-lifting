// Pattern: Count elements matching a condition
// Source: django-glitter/process_actions (count processed actions)
//         google-alerts/obfuscate (count obfuscated chars)
// Real-world: counting items in a collection that satisfy a filter

ghost function CountMatching(a: seq<int>, threshold: int): int
{
  if |a| == 0 then 0
  else (if a[|a|-1] >= threshold then 1 else 0) + CountMatching(a[..|a|-1], threshold)
}

method CountAboveThreshold(a: seq<int>, threshold: int) returns (count: int)
  ensures count == CountMatching(a, threshold)
{
  count := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant count == CountMatching(a[..i], threshold)
  {
    assert a[..i+1] == a[..i] + [a[i]];  // SMT QUIRK: B1 sequence extensionality
    if a[i] >= threshold {
      count := count + 1;
    }
    i := i + 1;
  }
  assert a[..|a|] == a;  // SMT QUIRK: B1 take-full
}
