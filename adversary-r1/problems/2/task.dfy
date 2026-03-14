/*
 * Problem 2: Multi-Loop Pipeline — Frequency Filter Reconstruction
 *
 * Given a sequence of integers and a threshold k, this method:
 *   Loop 1: Builds a frequency map counting occurrences of each element
 *   Loop 2: Filters the frequency map to find elements appearing >= k times
 *   Loop 3: Reconstructs an output sequence containing only elements from the
 *           input that appear >= k times, preserving original order
 *
 * The spec requires that the output is exactly the subsequence of input
 * elements whose frequency in the entire input meets the threshold.
 */

// Count occurrences of value v in sequence s
function CountOccurrences(s: seq<int>, v: int): int
  ensures CountOccurrences(s, v) >= 0
{
  if |s| == 0 then 0
  else (if s[0] == v then 1 else 0) + CountOccurrences(s[1..], v)
}

// The output should be the subsequence of input containing only
// elements that appear at least k times in the ENTIRE input.
ghost predicate FreqFilterSpec(input: seq<int>, k: int, output: seq<int>)
  requires k >= 1
{
  // output is a subsequence of input preserving order, containing exactly
  // those elements with count >= k
  IsOrderPreservingFilter(input, output, k)
}

// output is input filtered to elements with count >= k, preserving order
ghost predicate IsOrderPreservingFilter(input: seq<int>, output: seq<int>, k: int)
  requires k >= 1
{
  // There exists an injection from output indices to input indices
  // that is strictly increasing and maps to matching elements
  exists indices: seq<int> ::
    |indices| == |output| &&
    (forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |input|) &&
    (forall i :: 0 <= i < |indices| ==> input[indices[i]] == output[i]) &&
    (forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j]) &&
    // Every element of input with count >= k appears in output
    (forall i :: 0 <= i < |input| && CountOccurrences(input, input[i]) >= k ==>
      i in indices) &&
    // Every element of output has count >= k
    (forall i :: 0 <= i < |output| ==> CountOccurrences(input, output[i]) >= k)
}

method FreqFilter(input: seq<int>, k: int) returns (output: seq<int>)
  requires k >= 1
  ensures FreqFilterSpec(input, k, output)
{
  // Loop 1: Build frequency map
  var freq: map<int, int> := map[];
  var i := 0;
  while i < |input|
    // INVARIANT NEEDED HERE
  {
    var v := input[i];
    if v in freq {
      freq := freq[v := freq[v] + 1];
    } else {
      freq := freq[v := 1];
    }
    i := i + 1;
  }

  // Loop 2: Build set of frequent elements
  var frequentSet: set<int> := {};
  var keys := freq.Keys;
  // We need to iterate over the keys
  var keySeq: seq<int> := [];
  // Convert set to sequence
  var remaining := keys;
  while remaining != {}
    // INVARIANT NEEDED HERE
  {
    var x :| x in remaining;
    keySeq := keySeq + [x];
    remaining := remaining - {x};
  }

  var j := 0;
  while j < |keySeq|
    // INVARIANT NEEDED HERE
  {
    if keySeq[j] in freq && freq[keySeq[j]] >= k {
      frequentSet := frequentSet + {keySeq[j]};
    }
    j := j + 1;
  }

  // Loop 3: Reconstruct output preserving order
  output := [];
  var indices: seq<int> := [];
  var m := 0;
  while m < |input|
    // INVARIANT NEEDED HERE
  {
    if input[m] in frequentSet {
      output := output + [input[m]];
      indices := indices + [m];
    }
    m := m + 1;
  }
}
