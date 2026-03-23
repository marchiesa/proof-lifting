<|message|><DAFNY_CODE>
lemma SumAppend(a: seq<int>, i: nat)
  requires i < |a|
  ensures Sum(a[..i+1]) == Sum(a[..i]) + a[i]
{
  assert Sum(a[..i+1]) == a[i] + Sum(a[..i]);
}