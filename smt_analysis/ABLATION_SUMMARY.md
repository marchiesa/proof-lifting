# Ablation Summary: Essential Assertions in Dafny Verification

> **Note:** This document uses an earlier granular taxonomy (A-J). The
> canonical taxonomy used in the paper is in
> [`QUIRK_TAXONOMY.md`](QUIRK_TAXONOMY.md), with four high-level categories:
> A. E-matching (78, 43%), B. Missing axioms (52, 29%),
> C. Theory incompleteness (10, 5%), D. Propagation failures (42, 23%).

## Overview

We analyzed **104 verified Dafny programs** from the dataset. For each, we
extracted all assertions from method bodies (using the Dafny AST mapping) and
ablated each one to determine if it's essential for verification.

| Metric | Count |
|--------|-------|
| Problems analyzed | 104 |
| Problems with no assertions | 23 |
| Problems with assertions, all redundant | 29 |
| **Problems with essential assertions** | **52** (50%) |
| Total assertions across all problems | 985 |
| Essential assertions (raw, with duplicates) | 278 |
| **Essential assertions (unique)** | **182** |
| Redundant (non-essential) assertions | 707 |

An assertion is **essential** if removing it causes Dafny verification to fail
(error or timeout). A **redundant** assertion is one that can be removed without
affecting verification — it's implied by the remaining proof context.

## Distribution of Essential Assertions Per Problem

| Essential count | Problems |
|-----------------|----------|
| 0 | 52 |
| 1 | 11 |
| 2 | 17 |
| 3-5 | 7 |
| 6-8 | 12 |
| 10+ | 4 |
| 53 (0126_14_A) | 1 |

Most problems with essential assertions need only 1-2 (28/52). A few complex
problems (0126_14_A, 0003_1028_A, 0015_1064_A) need many.


## Taxonomy of Essential Assertions

All 182 unique essential assertions, organized by mechanism:

---

### A. Sequence Extensionality (50 assertions, 24 problems)

The single largest category. Z3 cannot discover certain sequence equalities on
its own because the relevant sequence axioms are guarded by trigger patterns
that don't fire. These assertions explicitly state equalities that Z3 should
(but cannot) derive from the built-in sequence theory.

#### A1. Take-Full-Length Identity (20 assertions, 19 problems)

```
assert a[..|a|] == a;
```

Z3 knows `Seq#Take(s, Seq#Length(s))` should equal `s`, but the axiom's trigger
pattern doesn't match in all contexts. This is the most common single pattern.

**Problems:** 0000_1013_A, 0009_1041_A, 0012_1060_A, 0028_1038_A, 0032_1136_A,
0035_1162_A, 0040_1159_A, 0045_1146_A, 0051_1095_A, 0054_1189_A, 0074_1220_A,
0079_1216_A, 0080_1281_A, 0096_1316_A, 0103_1305_A, 0104_1285_A, 0133_1385_B,
0136_1411_A, 0138_1413_A

#### A2. Take-Append Decomposition (15 assertions, 11 problems)

```
assert a[..i + 1] == a[..i] + [a[i]];
```

The fact that taking one more element equals the prefix plus the new element.
Z3 has the sequence axioms for this but the trigger `Seq#Take(s, i+1)` combined
with `Seq#Append(Seq#Take(s,i), Seq#Build(Seq#Index(s,i)))` doesn't fire.

**Problems:** 0000_1013_A, 0012_1060_A, 0031_1130_A, 0035_1162_A, 0040_1159_A,
0056_1178_A, 0079_1216_A, 0101_116_A, 0103_1305_A, 0133_1385_B, 0138_1413_A

#### A3. Take-of-Take / Prefix Preservation (8 assertions, 7 problems)

```
assert a[..i + 1][..i] == a[..i];
```

Taking a shorter prefix of a longer prefix yields the shorter prefix. Requires
composing two `Seq#Take` operations.

**Problems:** 0009_1041_A, 0028_1038_A, 0041_1143_A, 0045_1146_A, 0054_1189_A,
0069_1200_A, 0136_1411_A

#### A4. Take-Equals-Self (4 assertions, 3 problems)

```
assert a[..n] == a;  // where n == |a|
```

When the take index is a variable equal to length (not literally `|a|`), the
solver cannot connect `Seq#Take(a, n)` to `a` even though `n == |a|` is known.

**Problems:** 0031_1130_A, 0041_1143_A, 0069_1200_A

#### A5. Split-Concatenation (3 assertions, 3 problems)

```
assert a == a[..i] + a[i..];
assert a[..x] + a[x..y] == a[..y];
```

Splitting a sequence at a point and concatenating the pieces equals the whole.

**Problems:** 0032_1136_A, 0051_1095_A, 0103_1305_A

---

### B. Function Evaluation / Unfolding (22 assertions, 8 problems)

The solver cannot unfold user-defined function applications deeply enough or
cannot discover that two calls with different argument patterns produce the same
result.

#### B1. Function Symmetry / Commutativity (12 assertions, 3 problems)

```
assert FriendSum(a1, a2, a3, a4, true, true, false, false)
    == FriendSum(a1, a2, a3, a4, false, false, true, true);    // 7x in 0053_1230_A
assert CandiesAfterDivision(b, c, a, s) == maxCandies;          // 3x in 0068_1196_A
assert SwapCost(a, b, la, lb) == da + db;                       // 2x in 0085_1257_A
```

The solver cannot see that permuting arguments to a symmetric function gives
the same result without explicitly being told.

#### B2. Function-Variable Binding (7 assertions, 4 problems)

```
assert counts[minIdx] == CountChar(upper[minIdx], s);
assert CountIth(minIdx, s) == minCount;
assert CategoryRank(x + 0) == 0;
assert Gcd(wa, wb) == wa;
```

The solver cannot connect a variable's value (set earlier by computation) with
the result of re-evaluating the function. The function definition is correct but
the solver doesn't unfold it to verify the connection.

#### B3. Recursive Function Evaluation (3 assertions, 1 problem)

```
assert InitialList(n) == EvenList(0) + RangeSeq(1, n);
assert FinalList(n) == EvenList(n / 2);
assert |EvenList(n / 2)| == n / 2;
```

The solver needs to unfold recursive definitions more deeply than the default
fuel allows.

---

### C. Predicate Evaluation / Instantiation (28 assertions, 14 problems)

Non-equality assertions that force the solver to evaluate a predicate at specific
arguments, making the result available in the proof context.

#### C1. Complex Predicate Forcing (17 assertions, 8 problems)

```
assert IsValidSolution(x, y, z, a, b, c);       // 0132_1385_A, 6x
assert ValidAssignment(pens, pencils, a, b, c, d, k);  // 0077_1244_A
assert ValidDistribution(a, b, c, n, ...);       // 0107_1294_A
assert ValidChoice(y, b, r, m, m+1, m+2);        // 0024_1091_A
assert Feasible(a, b, c, rem, c2);               // 0066_1236_A
assert IsMinimalSide(a, b, val);                  // 0142_1360_A
assert ValidStep(a, c);                           // 0097_1311_A
```

The solver has all the facts but doesn't evaluate the predicate at the specific
argument combination needed for the postcondition.

#### C2. Collection Membership (5 assertions, 2 problems)

```
assert InSeq(a, sortedA);
assert !InSeq(a + b, A);
```

Membership in a sequence requires trigger matching that doesn't happen
automatically.

#### C3. Geometric / Domain-Specific Predicates (6 assertions, 1 problem)

```
assert CellInSquare(ly, gcc - ghalf, gcr, gcc, ghalf);
assert !CellInSquare(ly, rx, gcr, gcc, ghalf);
assert IsBlackSquareCenteredAt(n, m, grid, r - 1, c - 1, ghalf);
```

Only in 0003_1028_A (chess-board geometry). Complex predicate with many arguments.

---

### D. Bounds and Arithmetic (17 assertions, 6 problems)

#### D1. Arithmetic Bounds (11 assertions, 4 problems)

```
assert 1 <= r <= n;
assert a + b + c > 2 * m;
assert minutes >= 0;
assert k < m;
assert shares * minS <= r;
```

The solver needs explicit help with arithmetic inequality chains, especially
when multiple variables are involved or when the bound follows from a
combination of constraints.

#### D2. Modular/Division Arithmetic (6 assertions, 2 problems)

```
assert r - shares * minS == r % minS;
assert 0 <= m % k < k;
assert a % 3 == 0;
```

Z3's nonlinear arithmetic is incomplete. Relating multiplication/division/modulo
to each other requires explicit hints.

---

### E. Quantified Properties (14 assertions, 7 problems)

#### E1. Quantified Equalities (7 assertions, 5 problems)

```
assert forall j | 0 <= j < n :: ans[j] == EffectiveCap(j, h, restrictions);
assert forall q | 0 <= q < |old_result| :: result[q] == old_result[q];
assert forall j | x <= j < x + y :: t[j] == t[x];
```

Universal statements about equality across ranges. The solver cannot generalize
from individual instances.

#### E2. Quantified Non-Equalities (5 assertions, 3 problems)

```
assert forall x0, y0 :: !ValidAssignment(x0, y0, a, b, c, d, k);
assert forall c | 0 <= c < |grid[bot]| :: grid[bot][c] != '*';
assert forall j | 0 <= j < n :: Similar(w, s[j .. j + n]);
```

Universally quantified negations or properties. Often needed for postconditions
that assert "no other solution exists."

#### E3. Existential Witnesses (2 assertions, 1 problem)

```
assert exists c | left <= c < right :: grid[top][c] == '*';
assert exists r | top <= r < bottom :: grid[r][left] == '*';
```

The solver needs an explicit witness for an existential quantifier (only in
0126_14_A's grid problem).

---

### F. Indexing Equalities (13 assertions, 3 problems)

```
assert grid[ly][lx] == 'W';
assert newResult[w] == result[idx];
assert A[p] == A_before[p];
```

The solver knows the values at specific indices but cannot connect them when
the index expressions are complex or when array updates are involved. Mostly
concentrated in 0003_1028_A (9 of 13).

---

### G. Length Equalities (11 assertions, 5 problems)

```
assert |grid[r]| == m;
assert |upper| == k;
assert |x| == |a|;
```

The solver cannot determine sequence lengths, typically after construction via
comprehension or slicing.

---

### H. Multiset Equalities (3 assertions, 1 problem)

```
assert multiset(arr[..]) == multiset(a);
assert elems == multiset(a);
```

Only in 0110_1325_B (sorting). The multiset theory has limited automation.

---

### I. Case Split Completeness (6 assertions, 1 problem)

```
assert false;  // in unreachable branches
```

Only in 0003_1028_A. Used after establishing that all cases are covered, to tell
the solver an else branch is unreachable. The solver cannot derive this from the
preceding case analysis.

---

### J. Other Equalities (12 assertions, 3 problems)

```
assert ly == gcr - ghalf;
assert ry == gcr + ghalf + 1;
assert counted == crossSet;
assert s2 == p;
```

Simple variable equalities where the solver loses track of relationships between
ghost variables and computed values. Mostly in 0003_1028_A (8 of 12).


## Summary by Category

| Category | Assertions | Problems | % of all |
|----------|-----------|----------|----------|
| A. Sequence extensionality | 50 | 24 | 27.5% |
| B. Function evaluation | 22 | 8 | 12.1% |
| C. Predicate evaluation | 28 | 14 | 15.4% |
| D. Bounds/arithmetic | 17 | 6 | 9.3% |
| E. Quantified properties | 14 | 7 | 7.7% |
| F. Indexing equalities | 13 | 3 | 7.1% |
| G. Length equalities | 11 | 5 | 6.0% |
| H. Multiset equalities | 3 | 1 | 1.6% |
| I. Case splits | 6 | 1 | 3.3% |
| J. Other equalities | 12 | 3 | 6.6% |
| **Total** | **182** | **52** | |

Note: problem counts don't sum because one problem can have assertions in
multiple categories.


## Key Observations

1. **Sequence extensionality dominates.** 27.5% of all essential assertions and
   46% of all problems with essential assertions (24/52) need at least one
   sequence extensionality hint. The most common single pattern is
   `a[..|a|] == a` (20 instances across 19 problems).

2. **Most essential assertions are equalities.** 126/182 (69%) are equality
   assertions. The solver's core weakness is failing to discover equalities
   that follow from its own axioms.

3. **Predicate/function forcing is the second theme.** 50 assertions (27.5%)
   force the solver to evaluate a predicate or function at specific arguments.
   The solver has the definitions but doesn't instantiate them at the needed
   points.

4. **A few problems dominate the non-sequence categories.** Problem 0003_1028_A
   alone contributes 29 essential assertions (16% of all), mostly indexing,
   bounds, and case splits for a complex geometry proof. Problem 0126_14_A
   contributes 53 (but many are duplicates; 31 unique).

5. **Arithmetic is a minor issue.** Only 17 assertions (9.3%) relate to
   arithmetic reasoning. Nonlinear arithmetic (mod, division) accounts for 6.

6. **Half of all problems need no hints at all.** 52/104 problems verify with
   zero essential assertions. The LLM-added assertions in those cases are
   entirely redundant — useful for readability but not for the solver.


## Methodology

- **Source:** Each problem's `verified_inlined.dfy` (preferred) or `verified.dfy`
- **AST mapping:** Generated fresh with modified Dafny (`--ast-mapping`)
- **Assertion extraction:** Only `assert` statements in method bodies (not
  lemma bodies, not invariants, not requires/ensures)
- **Ablation:** Remove one assertion at a time, run `dafny verify` with 30s
  timeout. If verification fails → essential.
- **De-duplication:** Same (problem, line, text) counted once even if it appears
  in multiple AST methods.
