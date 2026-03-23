# A2 — Predicate Definition Not Applied Without Explicit Instantiation

## The quirk

A named predicate holds at specific arguments — the body is simple, the values are
concrete, and the fact is immediately obvious. But the verifier fails silently. The
fix is to add `assert P(args)` before the step that needs it.

The surprising part: Dafny predicates are **transparent** by default. Their bodies
are fully visible to Z3. Yet Z3 still will not apply the definition unless the
predicate term is explicitly introduced into the proof context.

## Why it happens

In Dafny's Boogie encoding, a ghost predicate `P(x) { body }` generates an axiom:

```
axiom ∀x :: P(x) ⟺ body(x)
```

The trigger for this axiom is the term `P(x)`. Z3 can only fire this axiom — either
to unfold `P` or to fold `body` into `P` — when `P(e)` appears as a term in the
e-graph for some concrete `e`.

If you never explicitly write `assert P(e)`, and no hypothesis or lemma result
places `P(e)` in the e-graph, then Z3 never applies the predicate's definition at
`e`. The body is visible but unreachable.

This matters most in two situations:

**1. Existential witness.** To prove `exists x :: P(x)`, Z3 must find a witness.
The natural candidate is some concrete `e` already in scope. But unless `P(e)` is
a ground term, Z3 will not instantiate the existential with `e` as witness — the
trigger for the existential never fires. Writing `assert P(e)` both verifies the
body at `e` and places `P(e)` in the e-graph, after which the existential proof is
immediate.

**2. Complex precondition.** When a lemma has `requires P(args)`, Dafny checks this
at the call site. But if `P`'s body involves several conjuncts, quantifiers, or
arithmetic that requires intermediate steps, the all-at-once check can fail. Writing
`assert P(args)` explicitly gives Z3 a focused subgoal to verify in isolation, and
then the precondition check degenerates to a trivial lookup.

## Why it is particularly surprising

**Transparency creates a false expectation.** Unlike languages where you must
"open" or "unfold" an abstract type, Dafny predicates are transparent by default.
A user naturally expects that if Dafny can see the definition, it will use it. The
gap between "can see" and "will use" is invisible: Dafny reports "postcondition
could not be proved" with no indication that the predicate body was never consulted.

**Even a two-value domain doesn't save you.** The most striking case is a predicate
over `bool`. Given `exists sw: bool :: P(sw)`, only two witnesses are possible. A
human would assume the verifier would simply try `false` and `true`. It does not.
Z3 does not enumerate domain values; it waits for a ground term `P(false)` or
`P(true)` to appear in the e-graph. Neither will appear without explicit help.

**The assertion seems vacuous.** When the predicate holds by simple arithmetic or
by an immediately provable case, writing `assert P(args)` looks like stating the
obvious. The user cannot tell whether the assertion is doing real work (introducing
a trigger ground term) or is merely documentation. Removing it silently breaks the
proof.

## The fix

Write the predicate instantiation explicitly before the step that needs it:

```dafny
assert P(concrete_args);   // places P(concrete_args) in e-graph
// now existential proofs, precondition checks, etc. can use it
```

In an existential proof, this often looks like:

```dafny
assert exists x :: P(x) by {
    assert P(witness);     // introduce ground term; proof of existential follows
}
```

Or simply, in a case-split proof, asserting the concrete instance in each branch:

```dafny
if condition_for_false {
    assert P(args, false);  // Z3 verifies the body; existential is now trivial
} else {
    assert P(args, true);
}
```

## Short examples

### Example 1: boolean witness (`BoolChoice`)

A predicate over `bool` has only two witnesses. The verifier still will not prove
the existential without an explicit assertion.

```dafny
ghost predicate Match(a: int, b: int, flag: bool)
{
  if flag then a == b + 1 else a == b - 1
}

lemma ShowExists(a: int, b: int)
  requires a == b + 1
  ensures exists flag: bool :: Match(a, b, flag)
{
  // Without this, the proof fails: Z3 won't enumerate flag ∈ {false, true}
  assert Match(a, b, true);
}
```

`ShowExistsFails` — omitting the assert — produces "a postcondition could not be
proved" even though substituting `flag = true` makes the body trivially true by
the precondition `a == b + 1`.

### Example 2: compound arithmetic predicate (`IsTriangle`)

A predicate with three conjuncts over arithmetic expressions. Even with a fully
concrete witness, Z3 will not prove the existential without an explicit predicate
assertion — it does not search for a satisfying instantiation on its own.

```dafny
ghost predicate IsTriangle(x: int, y: int, z: int)
{
  x + y > z && x + z > y && y + z > x
}

// Fails: Z3 needs a ground term IsTriangle(?, ?, ?) to instantiate the existential.
lemma ConstructTriangle_Fails()
  ensures exists x, y, z :: IsTriangle(x, y, z)
{ }

// Fix: assert the predicate at a concrete witness.
lemma ConstructTriangle_Fix()
  ensures exists x, y, z :: IsTriangle(x, y, z)
{
  assert IsTriangle(2, 2, 1);   // 2+2>1, 2+1>2, 2+1>2; now the existential fires
}
```

Without `assert IsTriangle(2, 2, 1)`, the verifier reports "postcondition could not
be proved" — even though (2, 2, 1) is a perfectly valid triangle. Z3 has no
mechanism to guess witnesses for open-ended existentials.

### Example 3: predicate needed as precondition hint

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
  // Direct call can fail if Z3 cannot verify InRange on complex expressions
  var mid := (a + b) / 2;
  assert InRange(mid, a, b);  // explicit instantiation: forces Z3 to check body
  UseRange(mid, a, b);         // now the precondition is a ground fact
}
```

## Connection to A1

A2 assertions frequently appear *inside* by-blocks that prove existentials (A1).
The structural pattern is:

```dafny
assert exists x :: P(x) by {
    assert P(witness);    // A2: predicate call at concrete arguments
}                          // A1: existential follows from the ground term
```

A1 and A2 are two sides of the same coin: A1 is the outer goal (the existential),
A2 is the inner step (the predicate instantiation that creates the witness ground
term).
