// Check if Two Sequences are Anagrams -- Reference solution with invariants

predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma SortedMultisetImpliesEqual(a: seq<int>, b: seq<int>)
  requires IsSorted(a) && IsSorted(b)
  requires multiset(a) == multiset(b)
  ensures a == b
  decreases |a|
{
  if |a| == 0 {
    assert |multiset(b)| == |multiset(a)| == 0;
    assert |b| == 0;
  } else {
    assert |b| == |a| by {
      assert |multiset(a)| == |a|;
      assert |multiset(b)| == |b|;
    }
    // Show a[0] == b[0]: both are mins of same multiset
    assert a[0] in multiset(a);
    assert a[0] in multiset(b);
    assert b[0] in multiset(b);
    assert b[0] in multiset(a);
    assert b[0] in a;
    assert a[0] in b;
    // a[0] <= all elements of a, b[0] <= all elements of b
    // a[0] is in b so a[0] >= b[0], b[0] is in a so b[0] >= a[0]
    assert a[0] == b[0];
    // Now prove tails have equal multisets
    assert a == [a[0]] + a[1..];
    assert b == [b[0]] + b[1..];
    // Use multiset calculation
    calc {
      multiset(a[1..]);
      == multiset(a) - multiset{a[0]};
      == multiset(b) - multiset{b[0]};
      == multiset(b[1..]);
    }
    SortedMultisetImpliesEqual(a[1..], b[1..]);
  }
}

method AreAnagrams(a: seq<int>, b: seq<int>) returns (result: bool)
  ensures result == (multiset(a) == multiset(b))
{
  if |a| != |b| {
    if multiset(a) == multiset(b) {
      assert |multiset(a)| == |a|;
      assert |multiset(b)| == |b|;
      assert false;
    }
    return false;
  }
  var sa := SortSeq(a);
  var sb := SortSeq(b);
  // If multisets are equal, sorted forms must be equal
  if multiset(a) == multiset(b) {
    assert multiset(sa) == multiset(sb);
    SortedMultisetImpliesEqual(sa, sb);
  }
  var i := 0;
  while i < |sa|
    invariant 0 <= i <= |sa|
    invariant |sa| == |sb|
    invariant forall j :: 0 <= j < i ==> sa[j] == sb[j]
    decreases |sa| - i
  {
    if sa[i] != sb[i] {
      assert sa != sb;
      if multiset(a) == multiset(b) {
        assert multiset(sa) == multiset(sb);
        SortedMultisetImpliesEqual(sa, sb);
        assert false;
      }
      result := false;
      return;
    }
    i := i + 1;
  }
  assert sa == sb;
  assert multiset(a) == multiset(sa) == multiset(sb) == multiset(b);
  result := true;
}

method SortSeq(s: seq<int>) returns (r: seq<int>)
  ensures |r| == |s|
  ensures IsSorted(r)
  ensures multiset(r) == multiset(s)
{
  var a := new int[|s|](i requires 0 <= i < |s| => s[i]);
  assert a[..] == s;
  InsertionSort(a);
  r := a[..];
}

method InsertionSort(a: array<int>)
  modifies a
  ensures IsSorted(a[..])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  if a.Length <= 1 { return; }
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant IsSorted(a[..i])
    invariant multiset(a[..]) == old(multiset(a[..]))
    decreases a.Length - i
  {
    var j := i;
    while j > 0 && a[j - 1] > a[j]
      invariant 0 <= j <= i
      invariant multiset(a[..]) == old(multiset(a[..]))
      invariant forall x, y :: 0 <= x < y <= i && y != j ==> a[x] <= a[y]
      decreases j
    {
      a[j - 1], a[j] := a[j], a[j - 1];
      j := j - 1;
    }
    i := i + 1;
  }
  assert a[..a.Length] == a[..];
}
