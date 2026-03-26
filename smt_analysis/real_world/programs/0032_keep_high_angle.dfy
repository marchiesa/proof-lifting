// Source: bartromgens/geojsoncontour/keep_high_angle
// URL: https://github.com/bartromgens/geojsoncontour/blob/79e30718fa0c1d96a2459eb1f45d06d699d240ed/geojsoncontour/utilities/multipoly.py#L46-L59
// Original: Keep vertices with angles higher than given minimum
// Gist: accepted = []; for v in vertices: if angle > min: accepted.append(v)

predicate AllAbove(s: seq<int>, threshold: int)
{
  forall i :: 0 <= i < |s| ==> s[i] > threshold
}

ghost function CountAbove(s: seq<int>, threshold: int): int
{
  if |s| == 0 then 0
  else (if s[|s|-1] > threshold then 1 else 0) + CountAbove(s[..|s|-1], threshold)
}

method KeepAboveThreshold(values: seq<int>, threshold: int) returns (accepted: seq<int>)
  ensures AllAbove(accepted, threshold)
  ensures |accepted| == CountAbove(values, threshold)
{
  accepted := [];
  var i := 0;
  while i < |values|
    invariant 0 <= i <= |values|
    invariant AllAbove(accepted, threshold)
    invariant |accepted| == CountAbove(values[..i], threshold)
  {
    assert values[..i+1] == values[..i] + [values[i]];
    if values[i] > threshold {
      accepted := accepted + [values[i]];
    }
    i := i + 1;
  }
  assert values[..|values|] == values;
}
