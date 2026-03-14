// Suffix Array Construction (Naive O(n^2 log n))
// Task: Add loop invariants so that Dafny can verify this program.
// Constructs suffix array: sorted order of all suffixes.

// Lexicographic comparison of suffixes starting at positions a and b
predicate LexLeq(s: seq<int>, a: int, b: int)
  requires 0 <= a <= |s|
  requires 0 <= b <= |s|
{
  a == b ||
  (exists k {:trigger s[a + k]} :: 0 <= k < |s| - a && 0 <= k < |s| - b &&
    (forall j {:trigger s[a + j]} :: 0 <= j < k ==> s[a + j] == s[b + j]) && s[a + k] < s[b + k]) ||
  (|s| - a <= |s| - b && forall j {:trigger s[a + j]} :: 0 <= j < |s| - a ==> s[a + j] == s[b + j])
}

predicate IsPermutation(sa: seq<int>, n: int)
{
  |sa| == n &&
  (forall i :: 0 <= i < n ==> 0 <= sa[i] < n) &&
  (forall i, j :: 0 <= i < j < n ==> sa[i] != sa[j])
}

method SuffixArray(s: seq<int>) returns (sa: seq<int>)
  requires |s| > 0
  ensures |sa| == |s|
  ensures IsPermutation(sa, |s|)
{
  var n := |s|;
  var arr := new int[n];
  var i := 0;
  while i < n
  {
    arr[i] := i;
    i := i + 1;
  }

  // Insertion sort on suffix indices by lexicographic order
  i := 1;
  while i < n
  {
    var key := arr[i];
    var j := i - 1;
    while j >= 0 && !LexLeq(s, arr[j], key)
    {
      arr[j + 1] := arr[j];
      j := j - 1;
    }
    arr[j + 1] := key;
    i := i + 1;
  }

  sa := arr[..];
}
