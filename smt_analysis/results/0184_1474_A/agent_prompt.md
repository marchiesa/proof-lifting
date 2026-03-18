Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Puzzle From the Future
In the $$$2022$$$ year, Mike found two binary integers $$$a$$$ and $$$b$$$ of length $$$n$$$ (both of them are written only by digits $$$0$$$ and $$$1$$$) that can have leading zeroes. In order not to forget them, he wanted to construct integer $$$d$$$ in the following way:

- he creates an integer $$$c$$$ as a result of bitwise summing of $$$a$$$ and $$$b$$$ without transferring carry, so $$$c$$$ may have one or more $$$2$$$-s. For example, the result of bitwise summing of $$$0110$$$ and $$$1101$$$ is $$$1211$$$ or the sum of $$$011000$$$ and $$$011000$$$ is $$$022000$$$;
- after that Mike replaces equal consecutive digits in $$$c$$$ by one digit, thus getting $$$d$$$. In the cases above after this operation, $$$1211$$$ becomes $$$121$$$ and $$$022000$$$ becomes $$$020$$$ (so, $$$d$$$ won't have equal consecutive digits).

Unfortunately, Mike lost integer $$$a$$$ before he could calculate $$$d$$$ himself. Now, to cheer him up, you want to find any binary integer $$$a$$$ of length $$$n$$$ such that $$$d$$$ will be maximum possible as integer.

Maximum possible as integer means that $$$102 > 21$$$, $$$012 < 101$$$, $$$021 = 21$$$ and so on.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0184_1474_A/task.dfy

```dafny
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
```

## Instructions:

1. Read the code carefully. Understand what the method does and what the spec requires.

2. Add loop invariants for every loop. Common patterns:
   - Bounds: `invariant 0 <= i <= |s|`
   - Accumulator: `invariant acc == F(s[..i])` for recursive ghost functions
   - Sequence slicing: `assert s[..i+1] == s[..i] + [s[i]];` before using F(s[..i+1])
   - Full slice identity: `assert s[..|s|] == s;` after loops that process entire sequences
   - Type preservation: `invariant AllNonNeg(s[..i])` if needed by the spec

3. Add helper lemmas if needed (e.g., SumAppend, induction lemmas).

4. Run dafny verify:
   ```bash
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0184_1474_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0184_1474_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0184_1474_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0184_1474_A/ (create the directory if needed).
