// Pattern: Transform each element of a list (map operation)
// Source: experimental/translate (translate tokens via dictionary)
//         acceptable/validate (convert errors to messages)
// Real-world: data transformation pipelines, format conversion

ghost function DoubleAll(s: seq<int>): seq<int>
{
  if |s| == 0 then []
  else DoubleAll(s[..|s|-1]) + [s[|s|-1] * 2]
}

method MapDouble(a: seq<int>) returns (result: seq<int>)
  ensures |result| == |a|
  ensures result == DoubleAll(a)
{
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant result == DoubleAll(a[..i])
  {
    assert a[..i+1] == a[..i] + [a[i]];  // SMT QUIRK: B1 sequence extensionality
    result := result + [a[i] * 2];
    i := i + 1;
  }
  assert a[..|a|] == a;  // SMT QUIRK: B1 take-full
}
