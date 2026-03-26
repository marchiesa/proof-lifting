// Source: interedition/collatex/_radixPass (prefix sum sub-step)
// URL: https://github.com/interedition/collatex/blob/76dd1fcc36047bc66a87d31142e72e98b5347821/collatex-pythonport/collatex/linsuffarr.py#L83-L136
// Original: Exclusive prefix sums for radix sort counting
// Gist: sum=0; for i in range(K+1): t=c[i]; c[i]=sum; sum+=t

ghost function Sum(s: seq<int>): int
{
  if |s| == 0 then 0 else Sum(s[..|s|-1]) + s[|s|-1]
}

method ExclusivePrefixSum(c: seq<int>) returns (result: seq<int>, total: int)
  ensures |result| == |c|
  ensures total == Sum(c)
  ensures forall i :: 0 <= i < |c| ==> result[i] == Sum(c[..i])
{
  result := [];
  total := 0;
  var i := 0;
  while i < |c|
    invariant 0 <= i <= |c|
    invariant |result| == i
    invariant total == Sum(c[..i])
    invariant forall j :: 0 <= j < i ==> result[j] == Sum(c[..j])
  {
    assert c[..i+1] == c[..i] + [c[i]];
    result := result + [total];
    total := total + c[i];
    i := i + 1;
  }
  assert c[..|c|] == c;
}
