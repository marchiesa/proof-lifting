# A1 — Existential-to-Existential Derivation Fails Across Equivalent Trigger Terms

## The quirk

Deriving one existential from another fails silently when the two existentials use
different but equivalent terms — even when the equivalence is immediately obvious
from the context.

Concretely: given `exists x :: P(e₁(x))` in context and a goal `exists x :: P(e₂(x))`,
if `e₁(x) == e₂(x)` holds for all relevant `x`, a human (or model) would consider
the goal trivially true. Z3 does not. The proof stalls unless explicit help is given.

## Why it happens

When a context existential `exists x :: P(e₁(x))` is in scope, Z3 introduces a
Skolem constant `x_sk` and adds `P(e₁(x_sk))` as a ground fact. The term `e₁(x_sk)`
enters the e-graph; `e₂(x_sk)` does not, even if `e₁ == e₂` holds.

To prove the goal `exists x :: P(e₂(x))`, Z3 needs a witness. The natural candidate
is `x_sk`, requiring `P(e₂(x_sk))` — but that term is absent from the e-graph.
E-matching for the goal trigger `e₂(x)` finds nothing to fire on.

Note: E-matching *is* performed up to the current congruence closure, so if
`e₁(x_sk)` and `e₂(x_sk)` are already in the same equivalence class, the trigger
*would* fire. The problem is that they reach the same class only after `e₂(x_sk)`
has been produced as a ground term — which is exactly what hasn't happened yet.

## Why it is particularly surprising

The failure occurs even when the equivalence `e₁ == e₂` is:

- **Definitional**: `f` and `g` have identical bodies (`f(n) = n+1`, `g(n) = n+1`)
- **Arithmetic**: `e₁ = bot`, `e₂ = bottom - 1`, with `bottom = bot + 1` in scope
- **Structural**: the same sequence indexed differently (`s[k]` vs `s[k'+1]` where `k = k'+1`)

In all cases the verifier treats the two terms as unrelated until something forces
`e₂(x_sk)` into the e-graph. The failure is invisible: Dafny simply reports
"postcondition could not be proved" with no indication of why.

## The fix is trivial — recognising the situation is not

The fix is exactly the standard mathematical proof: take a witness from the known
existential and use it to prove the goal existential. This is how any mathematician
would argue it on paper, without hesitation.

```
Given: exists x. P(e₁(x))
Take:  x_sk such that P(e₁(x_sk))          -- witness from hypothesis
Show:  P(e₂(x_sk))                          -- follows since e₁(x_sk) == e₂(x_sk)
Done:  exists x. P(e₂(x))                   -- by x_sk
```

The unsettling aspect is that you need to write this out at all. The verifier
offers no hint that a one-line witness construction is all that is missing.
Without understanding the trigger mechanism, the natural response is to add lemmas,
restructure invariants, or add auxiliary ghost state — none of which address the
actual problem.

## The two standard fixes in Dafny

**Fix 1 — by-body (explicit witness construction):**

```dafny
assert exists x :: P(e₂(x)) by {
    var x_sk :| P(e₁(x_sk));   // extract witness from hypothesis existential
    assert P(e₂(x_sk));         // follows by congruence: e₁(x_sk) == e₂(x_sk)
}
```

**Fix 2 — trigger substitution:**
Use `e₁(x)` as the trigger instead of `e₂(x)`. Since `e₁(x_sk)` is already in
the e-graph, the trigger fires immediately. Z3 evaluates the body `P(e₂(x_sk))`
using congruence closure. Counter-intuitively, the trigger does not need to appear
verbatim in the formula body.

```dafny
assert exists x {:trigger e₁(x)} :: P(e₂(x));
```

## Short examples

### Example 1: definitionally equal functions (`Obvious1`)

`f` and `g` have identical bodies. The goal is trivially true mathematically,
but Dafny cannot derive `P(g(k))` from `P(f(k))` without help.

```dafny
predicate P(x: nat)
function f(n: nat): nat { n + 1 }
function g(n: nat): nat { n + 1 }  // same body as f

lemma Obvious1(n: nat, m: nat)
  requires exists k | n <= k < m :: P(f(k))
  ensures  exists k | n <= k < m :: P(g(k))
{
  // Fix 1 — by-body:
  assert exists k | n <= k < m :: P(g(k)) by {
    var k :| n <= k < m && P(f(k));
    assert P(g(k));
  }
  // Fix 2 — trigger substitution (either suffices):
  // assert exists k {:trigger f(k)} | n <= k < m :: P(g(k));
}
```

For contrast, this variant verifies automatically because the witness `f(k)` is
already a ground term in the e-graph — no new function application is needed:

```dafny
lemma Obvious2(n: nat, m: nat)
  requires exists k | n <= k < m :: P(f(k))
  ensures  exists k | n <= k < m+1 :: P(k)   // goal is P(k), not P(g(k))
{}
```

### Example 2: index shift (`index_offset`)

The hypothesis has `P(s[k])` for `k` in `[1, |s|)`. The goal restates this as
`P(s[k+1])` for `k` in `[0, |s|-1)` — the same elements, shifted by one index.
Mathematically identical; Z3 cannot bridge it without a witness.

```dafny
method index_offset(s: seq<nat>)
  requires exists k | 1 <= k < |s| :: P(s[k])
  ensures  exists k {:trigger s[k+1]} | 0 <= k < |s| - 1 :: P(s[k+1])
{
  var k  :| 1 <= k < |s| && P(s[k]);  // extract witness
  var k' := k - 1;
  var _  := P(s[k' + 1]);              // force s[k'+1] into e-graph; equals s[k]
}
```

## A structural instance: the naming-split problem

A common real-world source of this quirk is a necessary naming split between a loop
variable and a derived variable. A backward scan loop naturally uses a scalar index
`bot` (giving loop invariants a trigger-friendly term `grid[bot][c]`), but callers
expect an exclusive upper bound `bottom = bot + 1` (giving postconditions the term
`grid[bottom-1][c]`). The split cannot be eliminated: rewriting invariants to use
`bottom - 1` directly causes Dafny to report "could not find a trigger" and the
invariant becomes unprovable, because arithmetic sub-expressions cannot serve as
trigger patterns.

The result is a structurally unavoidable mismatch between `e₁ = bot` (in the
invariant Skolem witness) and `e₂ = bottom - 1` (in the postcondition trigger).
See `examples.dfy` (`FindLastRow_*`) for a self-contained illustration.
