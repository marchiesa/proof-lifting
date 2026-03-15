// Counting Sort -- Reference solution with invariants

predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate InRange(s: seq<int>, k: int)
{
  forall i :: 0 <= i < |s| ==> 0 <= s[i] < k
}

predicate AllLeq(s: seq<int>, v: int)
{
  forall i :: 0 <= i < |s| ==> s[i] <= v
}

lemma AppendSorted(s: seq<int>, v: int)
  requires IsSorted(s)
  requires AllLeq(s, v)
  ensures IsSorted(s + [v])
  ensures AllLeq(s + [v], v)
{
  var t := s + [v];
  forall i, j | 0 <= i < j < |t| ensures t[i] <= t[j] {}
}

lemma MultisetOutOfRange(s: seq<int>, k: int, v: int)
  requires InRange(s, k)
  requires v < 0 || v >= k
  ensures multiset(s)[v] == 0
{
  if |s| > 0 {
    assert s == [s[0]] + s[1..];
    MultisetOutOfRange(s[1..], k, v);
  }
}

method CountingSort(a: seq<int>, k: int) returns (result: seq<int>)
  requires k > 0
  requires InRange(a, k)
  ensures IsSorted(result)
  ensures |result| == |a|
  ensures multiset(result) == multiset(a)
{
  var counts := new int[k](i => 0);

  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < k ==> counts[j] == multiset(a[..i])[j]
  {
    assert a[..i+1] == a[..i] + [a[i]];
    counts[a[i]] := counts[a[i]] + 1;
    i := i + 1;
  }
  assert a[..i] == a;
  ghost var fixedCounts := counts[..];

  result := [];
  var c := 0;
  while c < k
    invariant 0 <= c <= k
    invariant counts[..] == fixedCounts
    invariant forall j :: 0 <= j < k ==> fixedCounts[j] == multiset(a)[j]
    invariant IsSorted(result)
    invariant InRange(result, c)
    invariant c > 0 ==> AllLeq(result, c - 1)
    invariant forall j :: 0 <= j < c ==> multiset(result)[j] == multiset(a)[j]
    invariant forall j :: c <= j ==> multiset(result)[j] == 0
    decreases k - c
  {
    var j := 0;
    while j < counts[c]
      invariant 0 <= j <= counts[c]
      invariant counts[..] == fixedCounts
      invariant IsSorted(result)
      invariant AllLeq(result, c)
      invariant InRange(result, c + 1)
      invariant forall v :: 0 <= v < c ==> multiset(result)[v] == multiset(a)[v]
      invariant multiset(result)[c] == j
      invariant forall v :: c < v ==> multiset(result)[v] == 0
      decreases counts[c] - j
    {
      AppendSorted(result, c);
      result := result + [c];
      j := j + 1;
    }
    c := c + 1;
  }
  // Prove multiset equality
  forall v
    ensures multiset(result)[v] == multiset(a)[v]
  {
    if v < 0 || v >= k {
      MultisetOutOfRange(a, k, v);
    }
  }
  assert multiset(result) == multiset(a);
  // Prove length
  assert |result| == |multiset(result)| == |multiset(a)| == |a|;
}
