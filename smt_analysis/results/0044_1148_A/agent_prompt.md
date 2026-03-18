Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Another One Bites The Dust
Let's call a string good if and only if it consists of only two types of letters — 'a' and 'b' and every two consecutive letters are distinct. For example "baba" and "aba" are good strings and "abb" is a bad string.

You have $$$a$$$ strings "a", $$$b$$$ strings "b" and $$$c$$$ strings "ab". You want to choose some subset of these strings and concatenate them in any arbitrarily order.

What is the length of the longest good string you can obtain this way?

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0044_1148_A/task.dfy

```dafny
// A good string consists of only 'a' and 'b' with every two consecutive letters distinct.
ghost predicate IsGoodString(s: seq<char>)
{
  (forall i | 0 <= i < |s| :: s[i] == 'a' || s[i] == 'b') &&
  (forall i | 0 <= i < |s| - 1 :: s[i] != s[i+1])
}

// A good string with na 'a'-characters and nb 'b'-characters exists iff
// both counts are non-negative and they differ by at most 1.
ghost predicate GoodStringWithCounts(na: int, nb: int)
{
  na >= 0 && nb >= 0 && na - nb <= 1 && nb - na <= 1
}

// Whether a good string of exactly `len` characters can be formed by choosing
// some subset of the available pieces (at most a "a"s, b "b"s, c "ab"s)
// and concatenating them in some order.
//
// Selecting pa single-"a" pieces, pb single-"b" pieces, and pc "ab" pieces
// gives (pa + pc) total 'a'-characters and (pb + pc) total 'b'-characters,
// for a total length of pa + pb + 2*pc. A good string from these pieces
// exists iff the character counts differ by at most 1 — any such selection
// can be arranged into a valid good string.
ghost predicate AchievableLength(len: int, a: int, b: int, c: int)
{
  a >= 0 && b >= 0 && c >= 0 &&
  exists pa | 0 <= pa <= a ::
    exists pb | 0 <= pb <= b ::
      exists pc | 0 <= pc <= c ::
        GoodStringWithCounts(pa + pc, pb + pc) &&
        pa + pb + 2 * pc == len
}

method AnotherOneBitesTheDust(a: int, b: int, c: int) returns (maxLen: int)
  requires a >= 0 && b >= 0 && c >= 0
  ensures AchievableLength(maxLen, a, b, c)
  ensures forall n | maxLen < n <= a + b + 2 * c :: !AchievableLength(n, a, b, c)
{
  var x := a + c;
  var y := b + c;

  if x > y {
    x := y + 1;
  }
  if y > x {
    y := x + 1;
  }

  return x + y;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0044_1148_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0044_1148_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0044_1148_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0044_1148_A/ (create the directory if needed).
