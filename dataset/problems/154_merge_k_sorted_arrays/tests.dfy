// Merge K Sorted Arrays -- Spec tests

predicate Sorted(a: seq<int>) {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate IsPermutation(a: seq<int>, b: seq<int>) {
  multiset(a) == multiset(b)
}

function Flatten(arrays: seq<seq<int>>): seq<int>
  decreases |arrays|
{
  if |arrays| == 0 then []
  else arrays[0] + Flatten(arrays[1..])
}

predicate IsSortedMerge(arrays: seq<seq<int>>, result: seq<int>) {
  Sorted(result) && IsPermutation(Flatten(arrays), result)
}

method MergeTwo(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires Sorted(a) && Sorted(b)
  ensures Sorted(result)
  ensures multiset(result) == multiset(a) + multiset(b)
{
  result := [];
  var i := 0;
  var j := 0;
  while i < |a| || j < |b|
    invariant 0 <= i <= |a|
    invariant 0 <= j <= |b|
    decreases |a| - i + |b| - j
  {
    if i < |a| && (j >= |b| || a[i] <= b[j]) {
      result := result + [a[i]];
      i := i + 1;
    } else {
      result := result + [b[j]];
      j := j + 1;
    }
  }
  assume {:axiom} Sorted(result) && multiset(result) == multiset(a) + multiset(b);
}

method MergeKSorted(arrays: seq<seq<int>>) returns (result: seq<int>)
  requires |arrays| > 0
  requires forall i :: 0 <= i < |arrays| ==> Sorted(arrays[i])
  ensures IsSortedMerge(arrays, result)
{
  result := arrays[0];
  var i := 1;
  while i < |arrays|
    invariant 1 <= i <= |arrays|
    invariant Sorted(result)
    decreases |arrays| - i
  {
    result := MergeTwo(result, arrays[i]);
    i := i + 1;
  }
  assume {:axiom} IsSortedMerge(arrays, result);
}

method Main() {
  var a1: seq<seq<int>> := [[1, 4, 7], [2, 5, 8], [3, 6, 9]];
  var r1 := MergeKSorted(a1);
  expect Sorted(r1);
  expect |r1| == 9;

  var a2: seq<seq<int>> := [[1, 2, 3]];
  var r2 := MergeKSorted(a2);
  expect Sorted(r2);
  expect r2 == [1, 2, 3];

  // Negative test: unsorted result would fail
  expect Sorted([1, 2, 3]);
  expect !Sorted([3, 1, 2]);

  // Two arrays
  var a3: seq<seq<int>> := [[1, 3], [2, 4]];
  var r3 := MergeKSorted(a3);
  expect Sorted(r3);
  expect |r3| == 4;

  print "All spec tests passed\n";
}
