# A3 — Z3 Does Not Search for Existential Witnesses

## The quirk

The goal is `exists x :: P(x)`. The predicate body is simple, a witness is obviously
available — perhaps the entire domain satisfies `P`, or the domain has only two values.
The verifier fails silently. The fix is to assert `P(witness)` explicitly.

## Why it happens

Z3 is a **refutation solver**, not a search solver. To prove `exists x :: P(x)` it
negates the goal to `forall x :: !P(x)`, introduces a fresh Skolem constant `x_sk`,
and looks for a contradiction. It never enumerates candidate values for `x`.

This means that even when a witness is entirely obvious — `x = 0` trivially satisfies
`Small(x) { x <= 10 }`, or the domain is `{false, true}` — Z3 will not find it on
its own. The ground term `P(witness)` is simply absent from the e-graph, so neither
the definition axiom for `P` nor any relevant hypothesis ever fires at a positive
witness.

`assert P(witness)` places `P(witness)` in the e-graph. The definition axiom
`∀x :: P(x) ⟺ body(x)` fires, connecting `P(witness)` to `body(witness)`. With
`body(witness)` established, the existential `exists x :: P(x)` follows immediately
— it is now a ground fact rather than a search problem.

## Why it is particularly surprising

**The whole domain may satisfy `P`.** If `P(x)` holds for every `x` in the stated
range, a human would expect the verifier to trivially pick any element. Z3 does not
reason this way. The universally positive case is no easier than any other.

**A two-value domain doesn't save you.** With `exists flag: bool :: P(flag)`, only
`false` and `true` are possible. Z3 does not enumerate domain values; it waits for a
ground term to appear. Neither `P(false)` nor `P(true)` will appear without explicit
help.

**The assertion looks vacuous.** Writing `assert P(0)` when the predicate trivially
holds at `0` looks like stating the obvious. The user cannot tell whether the
assertion is doing real work (introducing a trigger term) or is mere documentation.
Removing it silently breaks the proof.

**The error message gives no hint.** Dafny reports "postcondition could not be proved"
with no indication that the predicate body was never evaluated at any positive witness.

## The fix

Assert a concrete witness before the existential:

```dafny
assert P(witness);   // places P(witness) in e-graph; existential follows
```

Or equivalently, wrap it in a `by`-block to make the proof structure explicit:

```dafny
assert exists x :: P(x) by {
    assert P(witness);
}
```

When no single witness covers all cases, split into branches and assert the
appropriate witness in each:

```dafny
if condition_for_witnessA {
    assert P(witnessA);
} else {
    assert P(witnessB);
}
```

## Relationship to A2

A3 is the specialisation of A2 to existential goals. The underlying mechanism is
identical: a ground term `P(witness)` is missing from the e-graph, so the definition
axiom `∀x :: P(x) ⟺ body(x)` never fires at a positive argument. A2 covers the
general case (firing any universally quantified axiom at specific arguments); A3 names
the particular surface pattern where the goal is an existential and the missing term
is the witness.
