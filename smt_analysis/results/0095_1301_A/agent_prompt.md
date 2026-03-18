Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Three Strings
You are given three strings $$$a$$$, $$$b$$$ and $$$c$$$ of the same length $$$n$$$. The strings consist of lowercase English letters only. The $$$i$$$-th letter of $$$a$$$ is $$$a_i$$$, the $$$i$$$-th letter of $$$b$$$ is $$$b_i$$$, the $$$i$$$-th letter of $$$c$$$ is $$$c_i$$$.

For every $$$i$$$ ($$$1 \leq i \leq n$$$) you must swap (i.e. exchange) $$$c_i$$$ with either $$$a_i$$$ or $$$b_i$$$. So in total you'll perform exactly $$$n$$$ swap operations, each of them either $$$c_i \leftrightarrow a_i$$$ or $$$c_i \leftrightarrow b_i$$$ ($$$i$$$ iterates over all integers between $$$1$$$ and $$$n$$$, inclusive).

For example, if $$$a$$$ is "code", $$$b$$$ is "true", and $$$c$$$ is "help", you can make $$$c$$$ equal to "crue" taking the $$$1$$$-st and the $$$4$$$-th letters from $$$a$$$ and the others from $$$b$$$. In this way $$$a$$$ becomes "hodp" and $$$b$$$ becomes "tele".

Is it possible that after these swaps the string $$$a$$$ becomes exactly the same as the string $$$b$$$?

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0095_1301_A/task.dfy

```dafny
// After swapping c[i] with a[i] (swapWithA=true) or b[i] (swapWithA=false),
// the resulting value at position i in string a
ghost function SwapResultA(a_i: char, c_i: char, swapWithA: bool): char
{
  if swapWithA then c_i else a_i
}

// The resulting value at position i in string b
ghost function SwapResultB(b_i: char, c_i: char, swapWithA: bool): char
{
  if swapWithA then b_i else c_i
}

// A swap direction is valid at position i if the resulting a[i] equals the resulting b[i]
ghost predicate ValidSwapChoice(a_i: char, b_i: char, c_i: char, swapWithA: bool)
{
  SwapResultA(a_i, c_i, swapWithA) == SwapResultB(b_i, c_i, swapWithA)
}

// The problem is solvable iff for every position there exists a swap direction
// (swap c[i] with a[i], or swap c[i] with b[i]) such that after all swaps, a == b.
// Since each position's swap is independent, this decomposes per position.
ghost predicate CanMakeEqual(a: string, b: string, c: string)
  requires |a| == |b| == |c|
{
  forall i | 0 <= i < |a| ::
    exists swapWithA: bool :: ValidSwapChoice(a[i], b[i], c[i], swapWithA)
}

method ThreeStrings(a: string, b: string, c: string) returns (result: bool)
  requires |a| == |b| == |c|
  ensures result == CanMakeEqual(a, b, c)
{
  var i := 0;
  while i < |a|
  {
    if a[i] != c[i] && b[i] != c[i] {
      return false;
    }
    i := i + 1;
  }
  return true;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0095_1301_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0095_1301_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0095_1301_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0095_1301_A/ (create the directory if needed).
