# A2 — Universal Quantifier Not Instantiated at Required Arguments

## The quirk

A named predicate holds at specific arguments — the body is simple, the values are
concrete, and the fact is immediately obvious. But the verifier fails silently. The
fix is to add `assert P(args)` before the step that needs it.

The surprising part: Dafny predicates are **transparent** by default. Their bodies
are fully visible to Z3. Yet Z3 still will not use the predicate at specific
arguments unless the term `P(args)` is explicitly placed in the proof context.

## Why it happens

Every use of a predicate's definition in Z3 — and every use of a universally
quantified hypothesis — goes through trigger-based quantifier instantiation.

In Dafny's Boogie encoding, a ghost predicate `P(x) { body }` generates an axiom:

```
axiom ∀x :: P(x) ⟺ body(x)
```

A universally quantified invariant or lemma postcondition generates a similar axiom:

```
axiom ∀j | guard(j) :: Q(j)
```

In both cases the trigger is the term that contains the quantified variable —
typically `P(x)` or `Q(j)`. Z3 only fires the axiom when a matching ground term
appears in the e-graph. Without it, the axiom sits unused.

`assert P(e)` places `P(e)` in the e-graph, firing whichever universal axioms have
`P` as a trigger component:

- The **definition axiom** `∀x :: P(x) ⟺ body(x)` fires, connecting `P(e)` to `body(e)`.
- Any **hypothesis or invariant** of the form `∀j :: ... P(a[j]) ...` fires at `j`
  such that `a[j] = e`, connecting the hypothesis to the specific index.

The A2 pattern therefore always involves a universal quantifier — either the
predicate's own definition axiom, a forall invariant, or both.

This matters most in two situations:

**1. Hypothesis instantiation.** When a forall hypothesis
`∀j :: guard(j) ==> Q(j)` needs to be applied at a specific index, the trigger
(typically some term involving `j`) must be in the e-graph. If `Q` involves a
predicate `P`, asserting `P(args_at_j)` puts the triggering ground term in the
e-graph, firing the hypothesis instantiation that produces the needed fact.

**2. Complex precondition.** When a lemma has `requires P(args)` and `P`'s body
involves several conjuncts or arithmetic, the all-at-once check at the call site
can exhaust Z3's heuristic budget. Writing `assert P(args)` explicitly gives Z3 a
focused subgoal, after which the precondition check is a trivial lookup.

(When the goal is existential — `exists x :: P(x)` — the same trigger mechanism
applies, but the missing ground term is specifically a positive witness. That case
is covered separately in **A3**.)

## Why it is particularly surprising

**Transparency creates a false expectation.** Unlike languages where you must
"open" or "unfold" an abstract type, Dafny predicates are transparent by default.
A user naturally expects that if Dafny can see the definition, it will use it. The
gap between "can see" and "will use" is invisible: Dafny reports "postcondition
could not be proved" with no indication that the predicate body was never consulted.

**The assertion seems vacuous.** When the predicate holds by simple arithmetic or
by an immediately provable case, writing `assert P(args)` looks like stating the
obvious. The user cannot tell whether the assertion is doing real work (introducing
a trigger ground term) or is merely documentation. Removing it silently breaks the
proof.

## The fix

Write the predicate instantiation explicitly before the step that needs it:

```dafny
assert P(concrete_args);   // places P(concrete_args) in e-graph
// now hypothesis firing, precondition checks, etc. can use it
```

## Short example

### Hypothesis instantiation (`ContradictForall`)

The hypothesis says `!Present(k)` for all `k` in `[0, n)`.
`Present(42)` is provably true. If `n > 42`, a contradiction exists — but only
once Z3 instantiates the forall at `k = 42`. The trigger for the forall is
`Present(k)`. Without `assert Present(42)`, the term `Present(42)` is never in
the e-graph and the trigger never fires.

```dafny
ghost predicate Present(x: int) { x == 42 }

// Fails: Present(42) never enters the e-graph; forall trigger at k=42 never fires.
lemma ContradictForall_Fails(n: int)
  requires n > 42
  requires forall k | 0 <= k < n :: !Present(k)
  ensures false
{ }

// Fix: assert Present(42) — fires the trigger, extracts !Present(42), derives false.
lemma ContradictForall_Fix(n: int)
  requires n > 42
  requires forall k | 0 <= k < n :: !Present(k)
  ensures false
{
  assert Present(42);
}
```

### Unreachable code (`CanExitAfter`)

After a loop that maintains `forall j | 0 <= j <= i :: !CanExitAfter(doors, j)`,
the code following the loop is unreachable (the loop always exits early). To prove
unreachability, Dafny must derive `false` by contradicting the invariant.

```dafny
assert doors[..n] == doors;
assert CanExitAfter(doors, n);   // A2: places CanExitAfter(doors,n) in e-graph
// invariant gives !CanExitAfter(doors, n) once the forall fires at j=n → false
return 0;   // unreachable; postcondition 1 <= k satisfied by contradiction
```

Without the assert, `CanExitAfter(doors, n)` is never a ground term. The forall
invariant's trigger never fires at `j = n`, so `!CanExitAfter(doors, n)` is never
extracted, and Z3 cannot construct the contradiction.

### Precondition hint

When a predicate appears in a `requires` clause, the call-site check can fail on
complex argument expressions even though the predicate body is simple. Explicitly
asserting the predicate first breaks the verification into a manageable subgoal.

```dafny
ghost predicate InRange(x: int, lo: int, hi: int)
{
  lo <= x < hi
}

lemma UseRange(x: int, lo: int, hi: int)
  requires InRange(x, lo, hi)
  ensures lo <= x
{ }

lemma CallSite(a: int, b: int)
  requires 0 < a < b
{
  var mid := (a + b) / 2;
  assert InRange(mid, a, b);  // explicit instantiation: forces Z3 to check body
  UseRange(mid, a, b);         // now the precondition is a ground fact
}
```

## The `forall`–`exists` invariant problem

A recurring manifestation of A2 is a loop invariant of the shape:

```dafny
invariant forall j | 0 <= j < i ::
            exists sw: bool :: P(a[j], b[j], c[j], sw)
```

This invariant cannot be maintained. Inside the loop body, the witness for `sw` is
established in two branches of an if-else — say `P(..., false)` in one branch and
`P(..., true)` in the other. At the branch merge point, neither is a definitive
ground term: Boogie retains only the conditional facts
`(cond ==> P(..., false)) && (!cond ==> P(..., true))`.

To prove `exists sw :: P(..., sw)` for the new index, Z3 needs to commit to a
specific Skolem witness for `sw`. It cannot extract one from a disjunction of
conditional facts — this requires a case split that Z3 does not perform automatically
in the invariant maintenance check.

A `forall` statement with `assume false` in the body does not help: the fact it
adds (`forall j :: ... ==> exists sw :: P(...)`) has the same nested-quantifier
shape. Z3 has difficulty using a `forall`–`exists` assumed fact to prove an
identical `forall`–`exists` goal because there is no Skolem ground term for the
inner existential.

**The fix**: avoid `exists` in the invariant. Instead use a disjunction over the
concrete witnesses (only possible when the witness domain is small, e.g. `bool`)
or name the existential as a separate predicate:

```dafny
// Option A — disjunction invariant (witness domain is {false, true}):
invariant forall j | 0 <= j < i ::
            P(a[j], b[j], c[j], true) || P(a[j], b[j], c[j], false)

// Option B — named predicate wrapping the existential:
ghost predicate HasWitness(a_j: T, b_j: T, c_j: T)
{
  exists sw: bool :: P(a_j, b_j, c_j, sw)
}
invariant forall j | 0 <= j < i :: HasWitness(a[j], b[j], c[j])
```

**Why option A works**: the disjunction `P(..., true) || P(..., false)` is
provable at the merge point via tautology — `cond || !cond` holds regardless of
which branch was taken, so the disjunction is derivable from the two conditional
facts without a committed witness.

**Why option B works**: `HasWitness(a[j], b[j], c[j])` is a plain predicate call
— no existential inside the invariant's `forall`. Z3 maintains and checks it as an
opaque ground term, deferring the existential unfolding to wherever `HasWitness` is
expanded (e.g. at the postcondition). When `HasWitness` is eventually unfolded,
the disjunction from the invariant provides the concrete witness.

The spec-level `CanMakeEqual` predicate is a direct example: changing
`forall i :: exists sw :: ValidSwapChoice(a[i], b[i], c[i], sw)` to
`forall i :: HasSwap(a[i], b[i], c[i])` (where `HasSwap` wraps the existential)
makes a previously unverifiable loop implementation verify with minimal annotation.

## Relationship to A1, A3, and the unified root cause

A1, A2, and A3 are surface-level distinctions over the same underlying mechanism:
**Z3 only instantiates universal quantifiers when a matching ground term is present
in the e-graph.**

- **A1** (existential witness via `by`-block): the goal is `exists x :: P(x)`. The
  fix is to provide a witness inside an explicit `by`-block.
- **A2** (predicate call for hypothesis/precondition): the missing ground term is
  `P(args)` at a specific argument, needed to fire a forall hypothesis or
  precondition check at that point.
- **A3** (Z3 does not search for witnesses): also about existentials, but highlights
  that Z3 never enumerates candidates — even trivial or finite domains.

The fix in all cases is identical — place the predicate at the required arguments
in the e-graph via an explicit assertion. A2 assertions frequently appear *inside*
by-blocks that prove existentials:

```dafny
assert exists x :: P(x) by {
    assert P(witness);    // A2: fires definition axiom at concrete arguments
}                          // A1/A3: existential follows from the resulting ground term
```
