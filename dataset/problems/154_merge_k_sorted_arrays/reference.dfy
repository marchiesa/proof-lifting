// Merge K Sorted Arrays -- Reference solution with invariants

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

lemma FlattenAppend(a: seq<seq<int>>, b: seq<seq<int>>)
  ensures Flatten(a + b) == Flatten(a) + Flatten(b)
  decreases |a|
{
  if |a| == 0 {
    assert a + b == b;
  } else {
    assert (a + b)[1..] == a[1..] + b;
    FlattenAppend(a[1..], b);
  }
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
    invariant Sorted(result)
    invariant multiset(result) == multiset(a[..i]) + multiset(b[..j])
    invariant |result| > 0 && i < |a| ==> result[|result|-1] <= a[i]
    invariant |result| > 0 && j < |b| ==> result[|result|-1] <= b[j]
    decreases |a| - i + |b| - j
  {
    if i < |a| && (j >= |b| || a[i] <= b[j]) {
      result := result + [a[i]];
      assert a[..i+1] == a[..i] + [a[i]];
      i := i + 1;
    } else {
      result := result + [b[j]];
      assert b[..j+1] == b[..j] + [b[j]];
      j := j + 1;
    }
  }
  assert a[..i] == a;
  assert b[..j] == b;
}

method MergeKSorted(arrays: seq<seq<int>>) returns (result: seq<int>)
  requires |arrays| > 0
  requires forall i :: 0 <= i < |arrays| ==> Sorted(arrays[i])
  ensures IsSortedMerge(arrays, result)
{
  // Iterative: fold left merge all arrays
  result := arrays[0];
  var i := 1;
  while i < |arrays|
    invariant 1 <= i <= |arrays|
    invariant Sorted(result)
    invariant multiset(result) == multiset(Flatten(arrays[..i]))
    decreases |arrays| - i
  {
    assert arrays[..i+1] == arrays[..i] + [arrays[i]];
    FlattenAppend(arrays[..i], [arrays[i]]);
    assert Flatten([arrays[i]]) == arrays[i] + Flatten([]);
    result := MergeTwo(result, arrays[i]);
    i := i + 1;
  }
  assert arrays[..i] == arrays;
}
