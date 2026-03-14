// Counting Sort -- Reference solution with invariants

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// Count occurrences of value v in sequence s
function CountOccurrences(s: seq<int>, v: int): int
{
  if |s| == 0 then 0
  else (if s[0] == v then 1 else 0) + CountOccurrences(s[1..], v)
}

lemma CountOccMultiset(s: seq<int>, v: int)
  ensures CountOccurrences(s, v) == if v in multiset(s) then multiset(s)[v] else 0
{
  if |s| > 0 {
    CountOccMultiset(s[1..], v);
    assert s == [s[0]] + s[1..];
  }
}

lemma CountOccAppend(s: seq<int>, v: int, x: int)
  ensures CountOccurrences(s + [x], v) == CountOccurrences(s, v) + (if x == v then 1 else 0)
{
  if |s| == 0 {
    assert s + [x] == [x];
  } else {
    assert (s + [x])[1..] == s[1..] + [x];
    CountOccAppend(s[1..], v, x);
  }
}

method CountingSort(a: seq<int>, maxVal: int) returns (result: seq<int>)
  requires maxVal > 0
  requires forall i :: 0 <= i < |a| ==> 0 <= a[i] < maxVal
  ensures IsSorted(result)
  ensures |result| == |a|
  ensures multiset(result) == multiset(a)
{
  // Count occurrences
  var counts := seq(maxVal, _ => 0);
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |counts| == maxVal
    invariant forall k :: 0 <= k < maxVal ==> counts[k] >= 0
    invariant forall k :: 0 <= k < maxVal ==> counts[k] == CountOccurrences(a[..i], k)
    decreases |a| - i
  {
    assert a[..i+1] == a[..i] + [a[i]];
    forall k {:trigger counts[k]} | 0 <= k < maxVal
      ensures counts[a[i] := counts[a[i]] + 1][k] == CountOccurrences(a[..i+1], k)
    {
      CountOccAppend(a[..i], k, a[i]);
    }
    counts := counts[a[i] := counts[a[i]] + 1];
    i := i + 1;
  }

  assert a[..i] == a;

  // Build result from counts
  result := [];
  var v := 0;
  while v < maxVal
    invariant 0 <= v <= maxVal
    invariant |counts| == maxVal
    invariant IsSorted(result)
    invariant forall x :: x in multiset(result) ==> 0 <= x < v
    invariant |result| > 0 ==> result[|result| - 1] < v
    invariant forall k :: 0 <= k < v ==> CountOccurrences(result, k) == CountOccurrences(a, k)
    invariant forall k :: v <= k < maxVal ==> CountOccurrences(result, k) == 0
    decreases maxVal - v
  {
    var c := 0;
    while c < counts[v]
      invariant 0 <= c <= counts[v]
      invariant |counts| == maxVal
      invariant IsSorted(result)
      invariant forall x :: x in multiset(result) ==> 0 <= x <= v
      invariant |result| > 0 ==> result[|result| - 1] <= v
      invariant forall k :: 0 <= k < v ==> CountOccurrences(result, k) == CountOccurrences(a, k)
      invariant CountOccurrences(result, v) == c
      invariant forall k :: v < k < maxVal ==> CountOccurrences(result, k) == 0
      decreases counts[v] - c
    {
      CountOccAppend(result, v, v);
      forall k | 0 <= k < maxVal && k != v
        ensures CountOccurrences(result + [v], k) == CountOccurrences(result, k)
      {
        CountOccAppend(result, k, v);
      }
      result := result + [v];
      c := c + 1;
    }
    assert CountOccurrences(result, v) == counts[v] == CountOccurrences(a, v);
    v := v + 1;
  }

  // Prove multiset equality
  assert multiset(result) == multiset(a) by {
    forall x
      ensures (x in multiset(result) ==> multiset(result)[x] == multiset(a)[x]) &&
              (x in multiset(a) ==> multiset(result)[x] == multiset(a)[x])
    {
      CountOccMultiset(result, x);
      CountOccMultiset(a, x);
      if 0 <= x < maxVal {
        assert CountOccurrences(result, x) == CountOccurrences(a, x);
      }
    }
  }

  // Prove length
  assert |result| == |a| by {
    assert multiset(result) == multiset(a);
    assert |multiset(result)| == |multiset(a)|;
  }
}
