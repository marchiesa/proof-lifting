function Sum(s: seq<int>): int {
  if |s| == 0 then 0 else s[|s|-1] + Sum(s[..|s|-1])
}

lemma SumAppend(a: seq<int>, i: nat)
  requires i < |a|
  ensures Sum(a[..i+1]) == Sum(a[..i]) + a[i]
{
  assert Sum(a[..i+1]) == Sum(a[..i]) + a[i];
}