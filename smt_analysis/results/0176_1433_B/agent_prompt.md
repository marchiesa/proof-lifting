Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Yet Another Bookshelf
There is a bookshelf which can fit $$$n$$$ books. The $$$i$$$-th position of bookshelf is $$$a_i = 1$$$ if there is a book on this position and $$$a_i = 0$$$ otherwise. It is guaranteed that there is at least one book on the bookshelf.

In one move, you can choose some contiguous segment $$$[l; r]$$$ consisting of books (i.e. for each $$$i$$$ from $$$l$$$ to $$$r$$$ the condition $$$a_i = 1$$$ holds) and:

- Shift it to the right by $$$1$$$: move the book at index $$$i$$$ to $$$i + 1$$$ for all $$$l \le i \le r$$$. This move can be done only if $$$r+1 \le n$$$ and there is no book at the position $$$r+1$$$.
- Shift it to the left by $$$1$$$: move the book at index $$$i$$$ to $$$i-1$$$ for all $$$l \le i \le r$$$. This move can be done only if $$$l-1 \ge 1$$$ and there is no book at the position $$$l-1$$$.

Your task is to find the minimum number of moves required to collect all the books on the shelf as a contiguous (consecutive) segment (i.e. the segment without any gaps).

For example, for $$$a = [0, 0, 1, 0, 1]$$$ there is a gap between books ($$$a_4 = 0$$$ when $$$a_3 = 1$$$ and $$$a_5 = 1$$$), for $$$a = [1, 1, 0]$$$ there are no gaps between books and for $$$a = [0, 0,0]$$$ there are also no gaps between books.

You have to answer $$$t$$$ independent test cases.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0176_1433_B/task.dfy

```dafny
// All positions in [l..r] hold a book
ghost predicate AllOnes(s: seq<int>, l: int, r: int)
{
  0 <= l <= r < |s| && forall i | l <= i <= r :: s[i] == 1
}

// A contiguous segment [l..r] of books can be shifted right by 1
ghost predicate CanShiftRight(s: seq<int>, l: int, r: int)
{
  AllOnes(s, l, r) && r + 1 < |s| && s[r + 1] == 0
}

// Result of shifting segment [l..r] right: leftmost vacated, right neighbor filled
ghost function ApplyShiftRight(s: seq<int>, l: int, r: int): seq<int>
  requires CanShiftRight(s, l, r)
{
  s[l := 0][r + 1 := 1]
}

// A contiguous segment [l..r] of books can be shifted left by 1
ghost predicate CanShiftLeft(s: seq<int>, l: int, r: int)
{
  AllOnes(s, l, r) && l - 1 >= 0 && s[l - 1] == 0
}

// Result of shifting segment [l..r] left: rightmost vacated, left neighbor filled
ghost function ApplyShiftLeft(s: seq<int>, l: int, r: int): seq<int>
  requires CanShiftLeft(s, l, r)
{
  s[r := 0][l - 1 := 1]
}

// All books form a single contiguous group (no 1...0...1 pattern)
ghost predicate BooksContiguous(s: seq<int>)
{
  forall i, j, k | 0 <= i < j < k < |s| :: !(s[i] == 1 && s[j] == 0 && s[k] == 1)
}

// Can the books in s be made contiguous in at most `steps` legal moves?
ghost predicate Reachable(s: seq<int>, steps: nat)
  decreases steps
{
  BooksContiguous(s)
  || (steps > 0
      && (exists l, r | 0 <= l <= r < |s| ::
            (CanShiftRight(s, l, r) && Reachable(ApplyShiftRight(s, l, r), steps - 1))
            || (CanShiftLeft(s, l, r) && Reachable(ApplyShiftLeft(s, l, r), steps - 1))))
}

method YetAnotherBookshelf(a: seq<int>) returns (moves: int)
  requires forall i | 0 <= i < |a| :: a[i] == 0 || a[i] == 1
  ensures moves >= 0 && Reachable(a, moves) && (moves == 0 || !Reachable(a, moves - 1))
{
  var n := |a|;
  var one := 0;
  var i := 0;
  while i < n {
    one := one + a[i];
    i := i + 1;
  }

  if one == 0 {
    return 0;
  }

  var first := 0;
  i := 0;
  while i < n {
    if a[i] == 1 {
      first := i;
      break;
    }
    i := i + 1;
  }

  var last := n;
  i := n - 1;
  while i >= 0 {
    if a[i] == 1 {
      last := i;
      break;
    }
    i := i - 1;
  }

  moves := last - first - one + 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0176_1433_B/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0176_1433_B/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0176_1433_B/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0176_1433_B/ (create the directory if needed).
