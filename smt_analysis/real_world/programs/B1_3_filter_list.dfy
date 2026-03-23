// Pattern: Filter a list, keeping only elements satisfying a condition
// Source: geojsoncontour/keep_high_angle (keep points with high angle)
//         elife-tools/text_to_title (keep non-stop words)
// Real-world: log filtering, data cleaning, permission filtering

ghost predicate AllPositive(s: seq<int>)
{
  forall i :: 0 <= i < |s| ==> s[i] > 0
}

method FilterPositive(a: seq<int>) returns (result: seq<int>)
  ensures AllPositive(result)
  ensures |result| <= |a|
{
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant AllPositive(result)
    invariant |result| <= i
  {
    if a[i] > 0 {
      assert AllPositive(result);  // SMT QUIRK: A2 predicate re-instantiation after append
      result := result + [a[i]];
    }
    i := i + 1;
  }
}
