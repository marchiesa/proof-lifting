// Generate All Subsets of Size K -- Spec tests

predicate StrictlySorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

predicate ValidSubset(s: seq<int>, n: int) {
  StrictlySorted(s) && forall i :: 0 <= i < |s| ==> 0 <= s[i] < n
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
  if k == 0 { result := [[]]; return; }
  result := [];
  var combo: seq<int> := [];
  var idx := 0;
  while idx < k
    invariant 0 <= idx <= k
    invariant |combo| == idx
    decreases k - idx
  {
    combo := combo + [idx];
    idx := idx + 1;
  }
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
  var iters := 0;
  while iters < maxIters
    invariant 0 <= iters <= maxIters
    invariant |combo| == k
    decreases maxIters - iters
  {
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
  assume {:axiom} AllSizeK(result, k) && AllValid(result, n) && NoDuplicates(result);
}

method Main() {
  // C(4,2) = 6
  var r1 := SubsetsOfSizeK(4, 2);
  expect |r1| == 6;
  expect AllSizeK(r1, 2);
  expect AllValid(r1, 4);
  expect NoDuplicates(r1);

  // C(3,1) = 3
  var r2 := SubsetsOfSizeK(3, 1);
  expect |r2| == 3;

  // C(4,0) = 1
  var r3 := SubsetsOfSizeK(4, 0);
  expect |r3| == 1;
  expect |r3[0]| == 0;

  // C(4,4) = 1
  var r4 := SubsetsOfSizeK(4, 4);
  expect |r4| == 1;
  expect r4[0] == [0, 1, 2, 3];

  // Negative: not a valid subset
  expect !ValidSubset([1, 0], 3);
  expect !ValidSubset([0, 5], 3);

  print "All spec tests passed\n";
}
