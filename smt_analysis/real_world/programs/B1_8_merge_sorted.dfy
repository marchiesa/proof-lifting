// Pattern: Merge two sorted arrays into one sorted array
// Source: sorting libraries, merge sort implementations
// Real-world: log merging, sorted data pipelines, time series merge

ghost function Count(a: seq<int>, v: int): int
{
  if |a| == 0 then 0
  else (if a[|a|-1] == v then 1 else 0) + Count(a[..|a|-1], v)
}

predicate Sorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method MergeSorted(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires Sorted(a) && Sorted(b)
  ensures Sorted(result)
  ensures |result| == |a| + |b|
{
  result := [];
  var i := 0;
  var j := 0;
  while i < |a| || j < |b|
    decreases |a| - i + |b| - j
    invariant 0 <= i <= |a| && 0 <= j <= |b|
    invariant |result| == i + j
    invariant Sorted(result)
    invariant |result| > 0 && i < |a| ==> result[|result|-1] <= a[i]
    invariant |result| > 0 && j < |b| ==> result[|result|-1] <= b[j]
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
