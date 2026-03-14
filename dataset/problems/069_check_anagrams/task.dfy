// Check if Two Sequences are Anagrams
// Task: Add loop invariants so that Dafny can verify this program.
// Uses counting approach: count occurrences of each element.

function CountOcc(s: seq<int>, x: int): nat
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == x then 1 else 0) + CountOcc(s[1..], x)
}

lemma CountOccConcat(a: seq<int>, b: seq<int>, x: int)
  ensures CountOcc(a + b, x) == CountOcc(a, x) + CountOcc(b, x)
  decreases |a|
{
  if |a| == 0 {
    assert a + b == b;
  } else {
    assert (a + b)[0] == a[0];
    assert (a + b)[1..] == a[1..] + b;
    CountOccConcat(a[1..], b, x);
  }
}

method AreAnagrams(a: seq<int>, b: seq<int>) returns (result: bool)
  ensures result == (multiset(a) == multiset(b))
{
  if |a| != |b| {
    assert multiset(a) != multiset(b) by {
      if multiset(a) == multiset(b) {
        assert |multiset(a)| == |multiset(b)|;
        assert |multiset(a)| == |a|;
        assert |multiset(b)| == |b|;
      }
    }
    return false;
  }
  // Sort both and compare
  var sa := SortSeq(a);
  var sb := SortSeq(b);
  var i := 0;
  while i < |sa|
  {
    if sa[i] != sb[i] {
      result := false;
      return;
    }
    i := i + 1;
  }
  result := true;
}

predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
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
  var i := 1;
  while i < a.Length
  {
    var j := i;
    while j > 0 && a[j - 1] > a[j]
    {
      a[j - 1], a[j] := a[j], a[j - 1];
      j := j - 1;
    }
    i := i + 1;
  }
}
