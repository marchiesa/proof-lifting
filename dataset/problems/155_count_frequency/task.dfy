// Count Frequency of Each Element
// Task: Add loop invariants so that Dafny can verify this program.

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
  // Every element in a is in the map with correct count
  (forall x :: x in freq ==> freq[x] == CountAll(a, x) && freq[x] > 0) &&
  // Every element present in a is a key
  (forall i :: 0 <= i < |a| ==> a[i] in freq) &&
  // No extra keys
  (forall x :: x in freq ==> CountAll(a, x) > 0)
}

method CountFrequency(a: seq<int>) returns (freq: map<int, nat>)
  ensures IsFrequencyMap(a, freq)
{
  freq := map[];
  var i := 0;
  while i < |a|
  {
    if a[i] in freq {
      freq := freq[a[i] := freq[a[i]] + 1];
    } else {
      freq := freq[a[i] := 1];
    }
    i := i + 1;
  }
}
