/*
 * Problem 2: Multi-Loop Pipeline — Frequency Filter Reconstruction
 */

function CountOccurrences(s: seq<int>, v: int): int
  ensures CountOccurrences(s, v) >= 0
{
  if |s| == 0 then 0
  else (if s[0] == v then 1 else 0) + CountOccurrences(s[1..], v)
}

ghost predicate FreqFilterSpec(input: seq<int>, k: int, output: seq<int>)
  requires k >= 1
{
  IsOrderPreservingFilter(input, output, k)
}

ghost predicate IsOrderPreservingFilter(input: seq<int>, output: seq<int>, k: int)
  requires k >= 1
{
  exists indices: seq<int> ::
    |indices| == |output| &&
    (forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |input|) &&
    (forall i :: 0 <= i < |indices| ==> input[indices[i]] == output[i]) &&
    (forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j]) &&
    (forall i :: 0 <= i < |input| && CountOccurrences(input, input[i]) >= k ==>
      i in indices) &&
    (forall i :: 0 <= i < |output| ==> CountOccurrences(input, output[i]) >= k)
}

// Lemma: CountOccurrences relates to splitting at a point
lemma CountOccurrencesSplit(s: seq<int>, v: int, n: int)
  requires 0 <= n <= |s|
  ensures CountOccurrences(s, v) == CountOccurrences(s[..n], v) + CountOccurrences(s[n..], v)
  decreases n
{
  if n == 0 {
    assert s[..0] == [];
    assert s[0..] == s;
  } else {
    assert s[..n] == [s[0]] + s[1..][..n-1];
    CountOccurrencesSplit(s[1..], v, n - 1);
    assert s[n..] == s[1..][n-1..];
  }
}

// Lemma: CountOccurrences of prefix grows by 0 or 1
lemma CountOccurrencesPrefixStep(s: seq<int>, v: int, n: int)
  requires 0 <= n < |s|
  ensures CountOccurrences(s[..n+1], v) == CountOccurrences(s[..n], v) + (if s[n] == v then 1 else 0)
{
  CountOccurrencesSplit(s[..n+1], v, n);
  assert (s[..n+1])[..n] == s[..n];
  assert (s[..n+1])[n..] == [s[n]];
}

// Lemma: freq map correctly counts occurrences after processing prefix
lemma {:induction false} FreqMapCorrect(input: seq<int>, freq: map<int, int>, n: int)
  requires 0 <= n <= |input|
  requires forall v :: v in freq <==> CountOccurrences(input[..n], v) > 0
  requires forall v :: v in freq ==> freq[v] == CountOccurrences(input[..n], v)
  ensures forall v :: v in freq ==> freq[v] == CountOccurrences(input[..n], v)
{}

method FreqFilter(input: seq<int>, k: int) returns (output: seq<int>)
  requires k >= 1
  ensures FreqFilterSpec(input, k, output)
{
  // Loop 1: Build frequency map
  var freq: map<int, int> := map[];
  var i := 0;
  while i < |input|
    invariant 0 <= i <= |input|
    invariant forall v :: v in freq <==> CountOccurrences(input[..i], v) > 0
    invariant forall v :: v in freq ==> freq[v] == CountOccurrences(input[..i], v)
  {
    var v := input[i];
    CountOccurrencesPrefixStep(input, v, i);
    // Also need to show that for other values, the count doesn't change
    forall u | u in freq && u != v
      ensures CountOccurrences(input[..i+1], u) == CountOccurrences(input[..i], u)
    {
      CountOccurrencesPrefixStep(input, u, i);
    }
    // And for values not in freq and != v
    forall u | u !in freq && u != v
      ensures CountOccurrences(input[..i+1], u) == CountOccurrences(input[..i], u)
    {
      CountOccurrencesPrefixStep(input, u, i);
    }
    if v in freq {
      freq := freq[v := freq[v] + 1];
    } else {
      freq := freq[v := 1];
    }
    i := i + 1;
  }

  // At this point: freq correctly counts occurrences in input[..i] == input[..|input|] == input
  assert input[..|input|] == input;
  assert forall v :: v in freq ==> freq[v] == CountOccurrences(input, v);
  assert forall v :: v in freq <==> CountOccurrences(input, v) > 0;

  // Loop 2: Build set of frequent elements
  // First: the freq map contains exactly the elements with count > 0
  // We need: frequentSet == {v | v in freq && freq[v] >= k}
  // Which equals {v | CountOccurrences(input, v) >= k}

  var frequentSet: set<int> := {};
  var keys := freq.Keys;
  var keySeq: seq<int> := [];
  var remaining := keys;
  while remaining != {}
    invariant remaining <= keys
    invariant forall x :: x in keySeq <==> x in keys && x !in remaining
    decreases remaining
  {
    var x :| x in remaining;
    keySeq := keySeq + [x];
    remaining := remaining - {x};
  }

  var j := 0;
  while j < |keySeq|
    invariant 0 <= j <= |keySeq|
    invariant forall x :: x in frequentSet ==> x in freq && freq[x] >= k
    invariant forall idx :: 0 <= idx < j ==> (keySeq[idx] in freq && freq[keySeq[idx]] >= k ==> keySeq[idx] in frequentSet)
  {
    if keySeq[j] in freq && freq[keySeq[j]] >= k {
      frequentSet := frequentSet + {keySeq[j]};
    }
    j := j + 1;
  }

  // Now prove frequentSet == {v | CountOccurrences(input, v) >= k}
  assert forall v :: v in frequentSet ==> CountOccurrences(input, v) >= k;
  assert forall v :: v in frequentSet ==> v in freq && freq[v] >= k;

  // Need: if CountOccurrences(input, v) >= k then v in frequentSet
  // CountOccurrences(input, v) >= k >= 1 > 0 ==> v in freq ==> v in keys ==> v in keySeq
  // Then since freq[v] >= k, v gets added to frequentSet

  assert forall x :: x in keySeq <==> x in keys;
  assert forall v :: CountOccurrences(input, v) >= k ==> v in freq;
  assert forall v :: v in freq <==> v in keys;

  // Need to know all keys elements are in keySeq
  // Then they were iterated over
  forall v | CountOccurrences(input, v) >= k
    ensures v in frequentSet
  {
    assert v in freq;
    assert v in keys;
    assert v in keySeq;
    // v is at some index in keySeq, so j passed over it
    var idx :| 0 <= idx < |keySeq| && keySeq[idx] == v;
    assert keySeq[idx] in freq && freq[keySeq[idx]] >= k;
  }

  // Now: frequentSet characterizes exactly the frequent elements
  assert forall v :: v in frequentSet <==> CountOccurrences(input, v) >= k;

  // Loop 3: Reconstruct output preserving order
  output := [];
  var indices: seq<int> := [];
  var m := 0;
  while m < |input|
    invariant 0 <= m <= |input|
    invariant |indices| == |output|
    invariant forall idx :: 0 <= idx < |indices| ==> 0 <= indices[idx] < m
    invariant forall idx :: 0 <= idx < |indices| ==> indices[idx] < |input|
    invariant forall idx :: 0 <= idx < |indices| ==> input[indices[idx]] == output[idx]
    invariant forall a, b :: 0 <= a < b < |indices| ==> indices[a] < indices[b]
    invariant forall idx :: 0 <= idx < m && CountOccurrences(input, input[idx]) >= k ==>
      idx in indices
    invariant forall idx :: 0 <= idx < |output| ==> CountOccurrences(input, output[idx]) >= k
    // Track that the last index is less than m (for monotonicity)
    invariant |indices| > 0 ==> indices[|indices|-1] < m
  {
    if input[m] in frequentSet {
      output := output + [input[m]];
      indices := indices + [m];
    }
    m := m + 1;
  }

  // Now prove the postcondition
  assert |indices| == |output|;
  assert forall idx :: 0 <= idx < |indices| ==> 0 <= indices[idx] < |input|;
  assert forall idx :: 0 <= idx < |indices| ==> input[indices[idx]] == output[idx];
  assert forall a, b :: 0 <= a < b < |indices| ==> indices[a] < indices[b];
  assert forall idx :: 0 <= idx < |input| && CountOccurrences(input, input[idx]) >= k ==>
    idx in indices;
  assert forall idx :: 0 <= idx < |output| ==> CountOccurrences(input, output[idx]) >= k;

  // Witness the existential
  assert IsOrderPreservingFilter(input, output, k) by {
    assert |indices| == |output|;
  }
}
