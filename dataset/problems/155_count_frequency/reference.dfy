// Count Frequency of Each Element -- Reference solution with invariants

function CountInSeq(a: seq<int>, x: int, n: int): nat
  requires 0 <= n <= |a|
  decreases n
{
  if n == 0 then 0
  else (if a[n-1] == x then 1 else 0) + CountInSeq(a, x, n - 1)
}

function CountAll(a: seq<int>, x: int): nat {
  CountInSeq(a, x, |a|)
}

predicate IsFrequencyMap(a: seq<int>, freq: map<int, nat>) {
  (forall x :: x in freq ==> freq[x] == CountAll(a, x) && freq[x] > 0) &&
  (forall i :: 0 <= i < |a| ==> a[i] in freq) &&
  (forall x :: x in freq ==> CountAll(a, x) > 0)
}

lemma CountStepLemma(a: seq<int>, x: int, n: int)
  requires 0 <= n < |a|
  ensures CountInSeq(a, x, n + 1) == CountInSeq(a, x, n) + (if a[n] == x then 1 else 0)
{
}

method CountFrequency(a: seq<int>) returns (freq: map<int, nat>)
  ensures IsFrequencyMap(a, freq)
{
  freq := map[];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall x :: x in freq ==> freq[x] == CountInSeq(a, x, i) && freq[x] > 0
    invariant forall j :: 0 <= j < i ==> a[j] in freq
    invariant forall x :: x in freq ==> CountInSeq(a, x, i) > 0
    invariant forall x :: x !in freq ==> CountInSeq(a, x, i) == 0
    decreases |a| - i
  {
    forall x | x in freq
      ensures CountInSeq(a, x, i + 1) == CountInSeq(a, x, i) + (if a[i] == x then 1 else 0)
    {
      CountStepLemma(a, x, i);
    }
    CountStepLemma(a, a[i], i);
    if a[i] in freq {
      freq := freq[a[i] := freq[a[i]] + 1];
    } else {
      freq := freq[a[i] := 1];
    }
    forall x | x !in freq
      ensures CountInSeq(a, x, i + 1) == 0
    {
      CountStepLemma(a, x, i);
    }
    i := i + 1;
  }
}
