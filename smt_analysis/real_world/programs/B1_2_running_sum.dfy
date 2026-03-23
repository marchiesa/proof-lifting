// Pattern: Compute running/cumulative sum of array
// Source: hic/qn (cumulative sum for Fourier coefficients)
//         python-libxdo/_radixPass (prefix sums for radix sort)
// Real-world: prefix sums, cumulative statistics, financial running totals

ghost function Sum(s: seq<int>): int
{
  if |s| == 0 then 0 else Sum(s[..|s|-1]) + s[|s|-1]
}

method PrefixSum(a: seq<int>) returns (result: seq<int>)
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |a| ==> result[i] == Sum(a[..i+1])
{
  result := [];
  var running := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant running == Sum(a[..i])
    invariant forall j :: 0 <= j < i ==> result[j] == Sum(a[..j+1])
  {
    assert a[..i+1] == a[..i] + [a[i]];  // SMT QUIRK: B1 sequence extensionality
    running := running + a[i];
    result := result + [running];
    i := i + 1;
  }
}
