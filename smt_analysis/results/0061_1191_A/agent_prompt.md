Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Tokitsukaze and Enhancement
Tokitsukaze is one of the characters in the game "Kantai Collection". In this game, every character has a common attribute — health points, shortened to HP.

In general, different values of HP are grouped into $$$4$$$ categories:

- Category $$$A$$$ if HP is in the form of $$$(4 n + 1)$$$, that is, when divided by $$$4$$$, the remainder is $$$1$$$;
- Category $$$B$$$ if HP is in the form of $$$(4 n + 3)$$$, that is, when divided by $$$4$$$, the remainder is $$$3$$$;
- Category $$$C$$$ if HP is in the form of $$$(4 n + 2)$$$, that is, when divided by $$$4$$$, the remainder is $$$2$$$;
- Category $$$D$$$ if HP is in the form of $$$4 n$$$, that is, when divided by $$$4$$$, the remainder is $$$0$$$.

The above-mentioned $$$n$$$ can be any integer.

These $$$4$$$ categories ordered from highest to lowest as $$$A > B > C > D$$$, which means category $$$A$$$ is the highest and category $$$D$$$ is the lowest.

While playing the game, players can increase the HP of the character. Now, Tokitsukaze wants you to increase her HP by at most $$$2$$$ (that is, either by $$$0$$$, $$$1$$$ or $$$2$$$). How much should she increase her HP so that it has the highest possible category?

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0061_1191_A/task.dfy

```dafny
// Maps HP to a category rank per the problem statement:
//   A (hp % 4 == 1) = 3, B (hp % 4 == 3) = 2, C (hp % 4 == 2) = 1, D (hp % 4 == 0) = 0
// Encoding the ordering A > B > C > D as 3 > 2 > 1 > 0.
ghost function CategoryRank(hp: int): int
  requires hp >= 1
{
  var r := hp % 4;
  if r == 1 then 3
  else if r == 3 then 2
  else if r == 2 then 1
  else 0
}

// Maps HP to its category character per the problem statement.
ghost function CategoryChar(hp: int): char
  requires hp >= 1
{
  var r := hp % 4;
  if r == 1 then 'A'
  else if r == 3 then 'B'
  else if r == 2 then 'C'
  else 'D'
}

method TokitsukazeAndEnhancement(x: int) returns (a: int, b: char)
  requires x >= 1
  // a is a valid increase (0, 1, or 2)
  ensures 0 <= a <= 2
  // b is the category of the resulting HP
  ensures b == CategoryChar(x + a)
  // No increase in {0,1,2} yields a strictly higher category
  ensures forall delta | 0 <= delta <= 2 :: CategoryRank(x + delta) <= CategoryRank(x + a)
  // a is the minimum increase achieving this best category
  ensures forall delta | 0 <= delta < a :: CategoryRank(x + delta) < CategoryRank(x + a)
{
  var r := x % 4;
  if r == 0 {
    a := 1;
    b := 'A';
  } else if r == 1 {
    a := 0;
    b := 'A';
  } else if r == 2 {
    a := 1;
    b := 'B';
  } else {
    a := 2;
    b := 'A';
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0061_1191_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0061_1191_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0061_1191_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0061_1191_A/ (create the directory if needed).
