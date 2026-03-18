/* === Specification: structural predicates modeling the problem === */

// A sequence is a permutation of {1, ..., n}: length n, all values
// in [1..n], and all values distinct.
ghost predicate IsPermutation(a: seq<int>, n: int)
{
  |a| == n && n >= 1 &&
  (forall i | 0 <= i < n :: 1 <= a[i] <= n) &&
  (forall i, j | 0 <= i < j < n :: a[i] != a[j])
}

// Position i is a peak: it is strictly interior and strictly greater
// than both its immediate neighbors.
ghost predicate IsPeak(a: seq<int>, i: int)
{
  0 < i < |a| - 1 && a[i] > a[i - 1] && a[i] > a[i + 1]
}

// Count the number of peaks in a sequence (slice-based recursion).
ghost function CountPeaks(a: seq<int>): int
  decreases |a|
{
  if |a| <= 2 then 0
  else CountPeaks(a[..|a| - 1]) + (if IsPeak(a, |a| - 2) then 1 else 0)
}

// Upper bound on peaks in any permutation of size n.
// Peaks must occupy interior positions (0 < i < n-1) and no two peaks
// can be adjacent — a[i] > a[i+1] and a[i+1] > a[i] is contradictory.
// This equals the maximum independent set on the path of (n-2)
// interior vertices, i.e. floor((n-1)/2).
ghost function MaxPeaks(n: int): int
{
  if n < 1 then 0 else (n - 1) / 2
}

/* === Method with specification === */

method ArrayAndPeaks(n: int, k: int) returns (result: seq<int>, possible: bool)
  ensures possible ==> IsPermutation(result, n) && CountPeaks(result) == k
  ensures !possible ==> result == [] && (n < 1 || k < 0 || k > MaxPeaks(n))
{
  var ma := (n - 1) / 2;
  if k > ma || k < 0 || n < 1 {
    result := [];
    possible := false;
  } else {
    var ans := new int[n];
    var idx := 0;
    while idx < n {
      ans[idx] := 0;
      idx := idx + 1;
    }

    var c := 0;
    var i := 1;
    while i < n && c < k {
      ans[i] := n - c;
      c := c + 1;
      i := i + 2;
    }

    var j := 1;
    i := 0;
    while i < n {
      if ans[i] == 0 {
        ans[i] := j;
        j := j + 1;
      }
      i := i + 1;
    }

    result := ans[..];
    possible := true;
  }
}