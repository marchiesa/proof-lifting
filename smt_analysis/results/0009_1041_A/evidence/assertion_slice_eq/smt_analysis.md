## Assertion: assert a[..i+1][..i] == a[..i];

### Dafny → SMT translation
- LHS: `a[..i+1][..i]` → `Seq#Take(Seq#Take(a#0, i#0 + 1), i#0)`
- RHS: `a[..i]` → `Seq#Take(a#0, i#0)`
- Boogie assertion (line 6209): `assert {:id "id253"} Seq#Equal(Seq#Take(Seq#Take(a#0, i#0 + 1), i#0), Seq#Take(a#0, i#0));`

### Relevant axioms and triggers

**Seq#Take axioms in the Boogie prelude:**

1. **Length**: `{ Seq#Length(Seq#Take(s, n)) }` → `Seq#Length(Seq#Take(s, n)) == n`
2. **Index**: `{ Seq#Index(Seq#Take(s, n), j) }` and `{ Seq#Index(s, j), Seq#Take(s, n) }` → element-by-element equality
3. **Take-of-Append**: `{ Seq#Take(Seq#Append(s, t), n) }` → only when `n == Seq#Length(s)`
4. **Take-of-Update**: Two variants for `i < n` and `i >= n`
5. **Take-zero**: `Seq#Take(s, 0) == Seq#Empty()`
6. **Drop-of-Drop**: `Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, m+n)` — exists for Drop, **NOT for Take**

**Seq#Equal**: Defined as length equality + pointwise index equality, with trigger `{ Seq#Equal(s0, s1) }`.

### What the failing VC contains

The loop body needs to prove invariant maintenance: `lo == SeqMin(a[..i'])` where `i' = i+1`.
SeqMin unfolds recursively on `a[..i+1]`, producing `SeqMin(a[..i+1][..|a[..i+1]|-1])` = `SeqMin(Seq#Take(Seq#Take(a, i+1), i))`.
To connect this to the old invariant `lo == SeqMin(a[..i])`, Z3 must prove `Seq#Take(Seq#Take(a, i+1), i) == Seq#Take(a, i)`.

### The gap

**Missing axiom: Take-of-Take simplification.** There is no axiom:
```
axiom (forall s: Seq, m: int, n: int ::
  { Seq#Take(Seq#Take(s, m), n) }
  0 <= n && n <= m && m <= Seq#Length(s)
     ==> Seq#Take(Seq#Take(s, m), n) == Seq#Take(s, n));
```

Note that the parallel `Drop-of-Drop` axiom DOES exist. This is an asymmetry in Boogie's sequence axiomatization.

Z3 could in principle prove the equality via `Seq#Equal` (length match + pointwise index equality), but:
- The `Seq#Equal` axiom only fires on `{ Seq#Equal(s0, s1) }` trigger — which doesn't appear without the assertion
- Even with ghost variables introducing the terms, the inner forall quantifier inside `Seq#Equal` requires additional trigger matching that Z3 doesn't explore automatically

**Ghost variable probe: FAILED** — confirming the solver needs the explicit equality, not just the terms.

### Confidence: HIGH
This is a clear case of a missing axiom in Boogie's sequence prelude.
