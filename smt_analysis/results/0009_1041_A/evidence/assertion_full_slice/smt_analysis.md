## Assertion: assert a[..|a|] == a;

### Dafny → SMT translation
- LHS: `a[..|a|]` → `Seq#Take(a#0, Seq#Length(a#0))`
- RHS: `a` → `a#0`
- Boogie assertion (line 6265): `assert {:id "id264"} Seq#Equal(Seq#Take(a#0, Seq#Length(a#0)), a#0);`

### Relevant axioms and triggers

**Seq#Take axioms in the Boogie prelude:**

1. **Length**: `{ Seq#Length(Seq#Take(s, n)) }` → `Seq#Length(Seq#Take(s, n)) == n`
2. **Index**: `{ Seq#Index(Seq#Take(s, n), j) }` and `{ Seq#Index(s, j), Seq#Take(s, n) }` → element-by-element
3. **Drop-zero**: `Seq#Drop(s, 0) == s` — exists for Drop, **NOT for Take-of-full-length**
4. **Take-of-Append**: Only fires when `n == Seq#Length(s)`, but requires an Append term

### What the failing VC contains

After loop exit with `i == |a|`, the invariants give:
- `lo == SeqMin(Seq#Take(a#0, i#0))` with `i#0 == Seq#Length(a#0)`
- So `lo == SeqMin(Seq#Take(a#0, Seq#Length(a#0)))`

FeasibilityLemma requires `lo == SeqMin(a#0)`.

To connect these, Z3 must prove `SeqMin(Seq#Take(a#0, Seq#Length(a#0))) == SeqMin(a#0)`, which requires `Seq#Take(a#0, Seq#Length(a#0)) == a#0`.

### The gap

**Missing axiom: Take-of-full-length identity.** There is no axiom:
```
axiom (forall s: Seq ::
  { Seq#Length(s) }
  Seq#Take(s, Seq#Length(s)) == s);
```

Note: `Seq#Drop(s, 0) == s` IS an axiom, so the dual identity exists for Drop but not for Take.

The Length and Index axioms are individually sufficient to prove the equality via `Seq#Equal`, but Z3's trigger-based matching doesn't explore this path automatically because:
1. No `Seq#Equal(Seq#Take(a, Seq#Length(a)), a)` term exists to fire the Seq#Equal trigger
2. The inner forall quantifier inside Seq#Equal needs Index terms that don't appear naturally

**Ghost variable probe: FAILED** — introducing `ghost var lhs := a[..|a|]; ghost var rhs := a;` without equality doesn't help.

### Confidence: HIGH
This is a clear case of a missing axiom in Boogie's sequence prelude.
