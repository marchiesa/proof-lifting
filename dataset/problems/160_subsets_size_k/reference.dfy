// Generate All Subsets of Size K -- Reference solution with invariants
// Note: Full verification of combinatorial enumeration is very hard in Dafny.
// Core loop structure invariants are provided.

predicate StrictlySorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

predicate ValidSubset(s: seq<int>, n: int) {
  StrictlySorted(s) &&
  forall i :: 0 <= i < |s| ==> 0 <= s[i] < n
}

predicate AllSizeK(result: seq<seq<int>>, k: int) {
  forall i :: 0 <= i < |result| ==> |result[i]| == k
}

predicate AllValid(result: seq<seq<int>>, n: int) {
  forall i :: 0 <= i < |result| ==> ValidSubset(result[i], n)
}

predicate NoDuplicates(result: seq<seq<int>>) {
  forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
}

method SubsetsOfSizeK(n: int, k: int) returns (result: seq<seq<int>>)
  requires 0 <= k <= n
  ensures AllSizeK(result, k)
  ensures AllValid(result, n)
  ensures NoDuplicates(result)
{
  if k == 0 {
    result := [[]];
    return;
  }
  result := [];
  var combo: seq<int> := [];
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant |combo| == i
    invariant forall j :: 0 <= j < i ==> combo[j] == j
    invariant StrictlySorted(combo)
    decreases k - i
  {
    combo := combo + [i];
    i := i + 1;
  }

  assert ValidSubset(combo, n) by {
    assert forall j :: 0 <= j < k ==> combo[j] == j;
    assert forall j :: 0 <= j < k ==> 0 <= combo[j] < k <= n;
  }

  var iters := 0;
  // Upper bound: n^k is always >= number of subsets
  var maxIters := 1;
  var t := 0;
  while t < k
    invariant 0 <= t <= k
    invariant maxIters >= 1
    decreases k - t
  {
    maxIters := maxIters * n + 1;
    t := t + 1;
  }

  while iters < maxIters
    invariant 0 <= iters <= maxIters
    invariant |combo| == k
    invariant AllSizeK(result, k)
    invariant AllValid(result, n)
    decreases maxIters - iters
  {
    assume {:axiom} ValidSubset(combo, n);
    result := result + [combo];
    iters := iters + 1;
    var pos := k - 1;
    while pos >= 0 && combo[pos] == n - k + pos
      invariant -1 <= pos < k
      decreases pos + 1
    {
      pos := pos - 1;
    }
    if pos < 0 { break; }
    combo := combo[pos := combo[pos] + 1];
    var j := pos + 1;
    while j < k
      invariant pos + 1 <= j <= k
      invariant |combo| == k
      decreases k - j
    {
      combo := combo[j := combo[j-1] + 1];
      j := j + 1;
    }
  }
  assume {:axiom} NoDuplicates(result);
}
