// --- Specification: modeling the problem structure ---

// A sequence is binary (all elements 0 or 1)
ghost predicate IsBinary(s: seq<int>) {
  forall i | 0 <= i < |s| :: s[i] == 0 || s[i] == 1
}

// 2^n, used to enumerate all binary sequences of length n
ghost function Pow2(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

// Convert integer k to a binary sequence of length n (big-endian)
// For 0 <= k < Pow2(n), this enumerates all binary sequences of length n
ghost function IntToBinary(k: int, n: int): (result: seq<int>)
  requires k >= 0
  requires n >= 0
  decreases n
  ensures |result| == n
{
  if n == 0 then []
  else IntToBinary(k / 2, n - 1) + [k % 2]
}

// Bitwise sum without carry: c[i] = a[i] + b[i]
// Each digit of c is in {0, 1, 2}
ghost function BitwiseSum(a: seq<int>, b: seq<int>): (result: seq<int>)
  requires |a| == |b|
  decreases |a|
  ensures |result| == |a|
{
  if |a| == 0 then []
  else BitwiseSum(a[..|a|-1], b[..|b|-1]) + [a[|a|-1] + b[|b|-1]]
}

// Replace consecutive equal digits by a single copy
ghost function Deduplicate(c: seq<int>): seq<int>
  decreases |c|
{
  if |c| == 0 then []
  else if |c| == 1 then c
  else if c[0] == c[1] then Deduplicate(c[1..])
  else [c[0]] + Deduplicate(c[1..])
}

// Compute d = Deduplicate(BitwiseSum(a, b))
ghost function ComputeD(a: seq<int>, b: seq<int>): seq<int>
  requires |a| == |b|
{
  Deduplicate(BitwiseSum(a, b))
}

// Strip leading zeros (for integer comparison)
ghost function StripLeadingZeros(d: seq<int>): seq<int>
  decreases |d|
{
  if |d| == 0 then []
  else if d[0] == 0 then StripLeadingZeros(d[1..])
  else d
}

// Lexicographic >= for equal-length digit sequences
ghost predicate LexGeq(s1: seq<int>, s2: seq<int>)
  requires |s1| == |s2|
  decreases |s1|
{
  if |s1| == 0 then true
  else if s1[0] != s2[0] then s1[0] > s2[0]
  else LexGeq(s1[1..], s2[1..])
}

// Integer comparison: d1 >= d2 as integers (strip leading zeros, compare)
ghost predicate IntGeq(d1: seq<int>, d2: seq<int>) {
  var s1 := StripLeadingZeros(d1);
  var s2 := StripLeadingZeros(d2);
  if |s1| != |s2| then |s1| > |s2|
  else LexGeq(s1, s2)
}

// a produces a d that is >= the d from every other binary sequence of length n
ghost predicate IsOptimalD(a: seq<int>, n: int, b: seq<int>)
  requires n >= 1
  requires |a| == n
  requires |b| == n
{
  forall k :: 0 <= k < Pow2(n) ==>
    IntGeq(ComputeD(a, b), ComputeD(IntToBinary(k, n), b))
}

// --- Method with specification ---

method PuzzleFromTheFuture(n: int, b: seq<int>) returns (a: seq<int>)
  requires n >= 1
  requires |b| == n
  requires IsBinary(b)
  ensures |a| == n
  ensures IsBinary(a)
  ensures IsOptimalD(a, n, b)
{
  a := [1];
  var i := 1;
  while i < n
  {
    if a[i - 1] + b[i - 1] == 1 + b[i] {
      a := a + [0];
    } else {
      a := a + [1];
    }
    i := i + 1;
  }
}