// Merge K Sorted Arrays (iterative pairwise merge)
// Task: Add loop invariants so that Dafny can verify this program.

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
  ensures Sorted(result) && IsPermutation(a + b, result)
{
  result := [];
  var i := 0;
  var j := 0;
  while i < |a| || j < |b|
  {
    if i < |a| && (j >= |b| || a[i] <= b[j]) {
      result := result + [a[i]];
      i := i + 1;
    } else {
      result := result + [b[j]];
      j := j + 1;
    }
  }
}

method MergeKSorted(arrays: seq<seq<int>>) returns (result: seq<int>)
  requires |arrays| > 0
  requires forall i :: 0 <= i < |arrays| ==> Sorted(arrays[i])
  ensures IsSortedMerge(arrays, result)
{
  var current := arrays;
  while |current| > 1
  {
    var next: seq<seq<int>> := [];
    var k := 0;
    while k < |current|
    {
      if k + 1 < |current| {
        var merged := MergeTwo(current[k], current[k+1]);
        next := next + [merged];
        k := k + 2;
      } else {
        next := next + [current[k]];
        k := k + 1;
      }
    }
    current := next;
  }
  result := current[0];
}
