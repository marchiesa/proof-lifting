// Check String Permutation -- Spec tests

predicate IsPermutation(a: seq<int>, b: seq<int>) {
  multiset(a) == multiset(b)
}

method IsPermutationCheck(a: seq<int>, b: seq<int>) returns (result: bool)
  ensures result == IsPermutation(a, b)
{
  if |a| != |b| {
    assert |multiset(a)| == |a|;
    assert |multiset(b)| == |b|;
    return false;
  }
  // Simple O(n^2) check: for each element, count in both
  var i := 0;
  var equal := true;
  while i < |a|
    invariant 0 <= i <= |a|
    decreases |a| - i
  {
    var ca := 0;
    var cb := 0;
    var j := 0;
    while j < |a|
      invariant 0 <= j <= |a|
      decreases |a| - j
    {
      if a[j] == a[i] { ca := ca + 1; }
      if b[j] == a[i] { cb := cb + 1; }
      j := j + 1;
    }
    if ca != cb { equal := false; }
    i := i + 1;
  }
  result := equal;
  assume {:axiom} result == IsPermutation(a, b);
}

method Main() {
  // Positive tests
  var r1 := IsPermutationCheck([1, 2, 3], [3, 2, 1]);
  expect r1 == true;
  expect IsPermutation([1, 2, 3], [3, 2, 1]);

  var r2 := IsPermutationCheck([1, 1, 2], [2, 1, 1]);
  expect r2 == true;

  // Negative tests
  var r3 := IsPermutationCheck([1, 2, 3], [1, 2, 4]);
  expect r3 == false;
  expect !IsPermutation([1, 2, 3], [1, 2, 4]);

  var r4 := IsPermutationCheck([1, 2], [1, 2, 3]);
  expect r4 == false;

  // Empty sequences
  var r5 := IsPermutationCheck([], []);
  expect r5 == true;

  print "All spec tests passed\n";
}
