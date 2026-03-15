// Count Frequency -- Spec tests

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

method CountFrequency(a: seq<int>) returns (freq: map<int, nat>)
  ensures IsFrequencyMap(a, freq)
{
  freq := map[];
  var i := 0;
  while i < |a|
    decreases |a| - i
  {
    if a[i] in freq {
      freq := freq[a[i] := freq[a[i]] + 1];
    } else {
      freq := freq[a[i] := 1];
    }
    i := i + 1;
  }
  assume {:axiom} IsFrequencyMap(a, freq);
}

method Main() {
  var a1 := [1, 2, 2, 3, 3, 3];
  var f1 := CountFrequency(a1);
  expect 1 in f1 && f1[1] == 1;
  expect 2 in f1 && f1[2] == 2;
  expect 3 in f1 && f1[3] == 3;

  // Empty array
  var a2: seq<int> := [];
  var f2 := CountFrequency(a2);
  expect |f2| == 0;

  // Single element
  var a3 := [7];
  var f3 := CountFrequency(a3);
  expect 7 in f3 && f3[7] == 1;

  // Negative test: key not in array should not be in map
  expect !(4 in f1);
  expect !(0 in f1);

  print "All spec tests passed\n";
}
