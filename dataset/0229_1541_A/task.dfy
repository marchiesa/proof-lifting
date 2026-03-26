// --- Specification: predicates and functions modeling the problem ---

ghost function Abs(x: int): int {
  if x >= 0 then x else -x
}

ghost function Min(a: int, b: int): int {
  if a <= b then a else b
}

// Total distance moved by all cats.
// perm[i] is the cat now at position i+1; that cat's original position was perm[i],
// so it moved |perm[i] - (i+1)| places.
ghost function TotalDistance(perm: seq<int>): int
  decreases |perm|
{
  if |perm| == 0 then 0
  else TotalDistance(perm[..|perm|-1]) + Abs(perm[|perm|-1] - |perm|)
}

// perm is a permutation of {1, ..., n}: length n, values in range, all distinct.
ghost predicate IsPermutation(perm: seq<int>, n: int) {
  |perm| == n &&
  (forall i | 0 <= i < n :: 1 <= perm[i] <= n) &&
  (forall i, j | 0 <= i < j < n :: perm[i] != perm[j])
}

// Derangement: no cat remains at its original position.
ghost predicate IsDerangement(perm: seq<int>, n: int) {
  |perm| == n &&
  (forall i | 0 <= i < n :: perm[i] != i + 1)
}

// Helper: the set {lo, lo+1, ..., hi}.
ghost function RangeSet(lo: int, hi: int): set<int> {
  if lo > hi then {} else {lo} + RangeSet(lo + 1, hi)
}

// Brute-force enumeration of all derangements to find the minimum total distance.
// Positions 0..pos-1 are already assigned (with accumulated cost partialDist).
// 'remaining' is the set of cat labels not yet placed.
// Returns the minimum total distance achievable over all valid completions
// that satisfy the derangement constraint.
ghost function MinDistHelper(n: int, pos: int, remaining: set<int>, partialDist: int): int
  requires 0 <= pos <= n
  decreases n - pos, n + 1
{
  if pos == n then partialDist
  else MinDistScan(n, pos, remaining, partialDist, 1)
}

// Scan candidate values v, v+1, ..., n for position pos.
// For each candidate that is available (in remaining) and satisfies the
// derangement constraint (v != pos+1), recurse on the remaining positions.
// Return the minimum total distance found across all valid completions.
ghost function MinDistScan(n: int, pos: int, remaining: set<int>, partialDist: int, v: int): int
  requires 0 <= pos < n
  requires 1 <= v
  decreases n - pos, n + 1 - v
{
  if v > n then
    n * n + 1  // sentinel larger than any valid total distance
  else
    var rest := MinDistScan(n, pos, remaining, partialDist, v + 1);
    if v in remaining && v != pos + 1 then
      var branch := MinDistHelper(n, pos + 1, remaining - {v},
                                   partialDist + Abs(v - (pos + 1)));
      Min(branch, rest)
    else
      rest
}

// The minimum total distance among all derangements of {1, ..., n}.
ghost function MinDerangementDistance(n: int): int
  requires n >= 2
{
  MinDistHelper(n, 0, RangeSet(1, n), 0)
}

// --- Methods (bodies unchanged) ---

method PrettyPermutation(n: int) returns (perm: seq<int>)
  requires n >= 2
  ensures IsPermutation(perm, n)
  ensures IsDerangement(perm, n)
  ensures TotalDistance(perm) == MinDerangementDistance(n)
{
  if n % 2 == 0 {
    perm := [2, 1];
    var i := 4;
    while i <= n {
      perm := perm + [i, i - 1];
      i := i + 2;
    }
  } else {
    perm := [3, 1, 2];
    var i := 5;
    while i <= n {
      perm := perm + [i, i - 1];
      i := i + 2;
    }
  }
}

method ComputeExpected(n: int) returns (expected: seq<int>)
{
  if n % 2 == 0 {
    expected := [];
    var i := 0;
    while i < n {
      expected := expected + [i + 2, i + 1];
      i := i + 2;
    }
  } else {
    expected := [3, 1, 2];
    var i := 3;
    while i < n {
      expected := expected + [i + 2, i + 1];
      i := i + 2;
    }
  }
}