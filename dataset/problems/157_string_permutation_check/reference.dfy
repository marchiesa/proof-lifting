// Check String Permutation -- Reference solution with invariants

predicate IsPermutation(a: seq<int>, b: seq<int>) {
  multiset(a) == multiset(b)
}

predicate Sorted(a: seq<int>) {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

lemma SortedEqualMultisetEqual(a: seq<int>, b: seq<int>)
  requires Sorted(a) && Sorted(b)
  requires |a| == |b|
  requires forall i :: 0 <= i < |a| ==> a[i] == b[i]
  ensures multiset(a) == multiset(b)
{
  assert a == b;
}

lemma SortedDifferentMultisetDifferent(a: seq<int>, b: seq<int>, k: int)
  requires Sorted(a) && Sorted(b)
  requires |a| == |b|
  requires 0 <= k < |a| && a[k] != b[k]
  requires forall i :: 0 <= i < k ==> a[i] == b[i]
  ensures multiset(a) != multiset(b)
{
  if a[k] < b[k] {
    // count of a[k] in a[k..] is >= 1
    // but count of a[k] in b[k..] is 0 since b is sorted and b[k] > a[k]
    assert a[k] in multiset(a);
    var countA := multiset(a)[a[k]];
    var countB := multiset(b)[a[k]];
    // In a[..k] and b[..k] same count since equal
    // In a[k..], a[k] appears at least once
    // In b[k..], all elements >= b[k] > a[k], so a[k] doesn't appear
    assert multiset(a[k..])[a[k]] >= 1;
    assert forall i :: k <= i < |b| ==> b[i] >= b[k] > a[k];
    assert multiset(b[k..])[a[k]] == 0;
    assert a == a[..k] + a[k..];
    assert b == b[..k] + b[k..];
    assert a[..k] == b[..k];
  } else {
    assert b[k] < a[k];
    assert b[k] in multiset(b);
    assert multiset(b[k..])[b[k]] >= 1;
    assert forall i :: k <= i < |a| ==> a[i] >= a[k] > b[k];
    assert multiset(a[k..])[b[k]] == 0;
    assert a == a[..k] + a[k..];
    assert b == b[..k] + b[k..];
    assert a[..k] == b[..k];
  }
}

method Sort(a: seq<int>) returns (result: seq<int>)
  ensures Sorted(result)
  ensures multiset(a) == multiset(result)
{
  result := a;
  var i := 0;
  while i < |result|
    invariant 0 <= i <= |result|
    invariant multiset(a) == multiset(result)
    invariant forall j, k :: 0 <= j < i <= k < |result| ==> result[j] <= result[k]
    invariant forall j, k :: 0 <= j < k < i ==> result[j] <= result[k]
    decreases |result| - i
  {
    var minIdx := i;
    var j := i + 1;
    while j < |result|
      invariant i <= minIdx < j <= |result|
      invariant forall k :: i <= k < j ==> result[minIdx] <= result[k]
      decreases |result| - j
    {
      if result[j] < result[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    if minIdx != i {
      var tmp := result[i];
      result := result[i := result[minIdx]][minIdx := tmp];
    }
    i := i + 1;
  }
}

method IsPermutationCheck(a: seq<int>, b: seq<int>) returns (result: bool)
  ensures result == IsPermutation(a, b)
{
  if |a| != |b| {
    assert multiset(a) != multiset(b) by {
      if |a| < |b| {
        assert |multiset(a)| == |a| < |b| == |multiset(b)|;
      } else {
        assert |multiset(a)| == |a| > |b| == |multiset(b)|;
      }
    }
    return false;
  }
  var sa := Sort(a);
  var sb := Sort(b);
  assert |sa| == |a| && |sb| == |b| by {
    assert |multiset(a)| == |a|;
    assert |multiset(sa)| == |sa|;
    assert |multiset(b)| == |b|;
    assert |multiset(sb)| == |sb|;
  }
  var i := 0;
  while i < |sa|
    invariant 0 <= i <= |sa|
    invariant |sa| == |sb|
    invariant forall k :: 0 <= k < i ==> sa[k] == sb[k]
    decreases |sa| - i
  {
    if sa[i] != sb[i] {
      SortedDifferentMultisetDifferent(sa, sb, i);
      return false;
    }
    i := i + 1;
  }
  SortedEqualMultisetEqual(sa, sb);
  result := true;
}
