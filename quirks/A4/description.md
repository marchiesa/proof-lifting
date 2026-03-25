# A4 — Universal Fact Not Synthesized from Individual Element Facts

## The quirk

The solver can verify a claim `P(e)` for any specific element `e`, and all the
necessary ingredients are in scope. But it cannot lift those individual facts into
a universally quantified statement `∀i :: P(i)` on its own. The fix is to write
an explicit `assert forall i :: P(i)`, optionally with a `by`-block or a ghost
`forall` statement.

## Why it happens

Z3's e-matching works **top-down**: given a universally quantified axiom
`∀x :: P(x)`, it waits for a ground term matching the trigger to appear and then
instantiates. It does not work **bottom-up**: it will not observe a collection of
ground facts `P(0), P(1), ..., P(n-1)` and infer `∀i | 0 <= i < n :: P(i)`.

Concretely, this arises in a loop when:

1. A sequence is updated: `result := old_result + [new_elem]`.
   The solver knows `result[i] == old_result[i]` for each `i` because it can
   instantiate the sequence prelude axiom at any specific index. But the loop
   invariant is phrased as `forall q :: result[q] == old_result[q]`. The
   universal form is not automatically derived from the append equation.

2. A universally quantified invariant needs to be re-established after an
   update. The solver proves `Inv[j := v]` holds for the updated state at any
   specific index, but fails to re-establish `∀i :: Inv[i]` over the whole
   updated collection without an explicit intermediate step.

In both cases, the verification condition that Dafny emits requires Z3 to produce
a universally quantified fact. Z3's engine does not "generalize" from ground facts;
it can only close a `∀` goal by verifying it from axioms directly. When the needed
reasoning is implicit (e.g., "use the append axiom at every index"), Z3 times out
or fails without a hint.

The explicit `assert forall` acts as an intermediate lemma checkpoint: Dafny
emits a focused verification condition for the `forall` assertion alone, Z3
proves it (often trivially, via a single axiom instantiation), and the result
becomes a new ground fact available for subsequent steps.

## Why it is particularly surprising

**The universal fact seems tautological.** After `result := old + [x]`, the
claim `forall i | 0 <= i < |old| :: result[i] == old[i]` follows directly from
the sequence append definition. A user would not expect to state something so
obvious. Yet without it, the next loop invariant maintenance check fails.

**Explicit triggers are sometimes required.** Even when the `assert forall`
is written, Z3 may still fail if it cannot figure out a matching term. Adding
`{:trigger result[i]}` or `{:trigger old[i]}` resolves this by telling Z3
exactly what ground term pattern should trigger the universal instantiation in
downstream reasoning.

**The `forall` statement is not the same as the `assert forall`.** Dafny has
two different constructs:
- `forall i | P :: ensures Q { ... }` — a ghost statement that proves `∀i :: P ==> Q` and adds it as a fact.
- `assert forall i :: Q;` — an assertion that Dafny checks holds and makes available as a fact.

Both can introduce universal facts. The choice depends on whether a proof body
is needed.

## The fix

After any sequence or array update inside a loop, bridge the old and new states
with an explicit `assert forall`:

```dafny
ghost var prev := result;
result := result + [new_elem];
assert forall i {:trigger result[i]} | 0 <= i < |prev| :: result[i] == prev[i];
// loop invariant about result can now use this fact
```

For more complex universals, use a ghost `forall` statement with a proof body:

```dafny
forall i | 0 <= i < n
  ensures P(a[i])
{
  // prove P(a[i]) for a specific i
}
// now assert forall i :: P(a[i]) is available
```

## Short examples

### U1: element-wise equality after sequence append

```dafny
method Collect(n: int) returns (result: seq<int>)
  requires n >= 0
  ensures |result| == n
  ensures forall i | 0 <= i < n :: result[i] == i
{
  result := [];
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant |result| == k
    invariant forall i | 0 <= i < k :: result[i] == i
  {
    ghost var prev := result;
    result := result + [k];
    // Without this, the invariant for i < k fails: solver knows
    // result == prev + [k] but won't unfold to the universal.
    assert forall i {:trigger result[i]} | 0 <= i < |prev| :: result[i] == prev[i];
    k := k + 1;
  }
}
```

### U2: forall needed to match an invariant's trigger shape

After a loop builds `newResult` from `result` filtered by `stops[k]`, the
next iteration's invariant requires:

```
forall x :: (forall m | 0 <= m < k+1 :: InSeq(x, stops[m])) ==> InSeq(x, newResult)
```

The solver has individual facts about specific elements but cannot produce the
nested `∀∀`-implication automatically. The fix:

```dafny
assert forall x :: (forall m | 0 <= m < k + 1 :: InSeq(x, stops[m])) ==> InSeq(x, newResult)
by {
  forall x | (forall m | 0 <= m < k + 1 :: InSeq(x, stops[m]))
    ensures InSeq(x, newResult)
  {
    // use loop invariant and individual InSeq facts for specific x
    assert InSeq(x, result);
    ...
  }
}
```

## Relationship to A2

A2 and A4 are complementary directions over the same E-matching mechanism:

- **A2** fires a *known* universal axiom `∀x :: P(x)` at a specific ground term —
  the direction is ∀ → ground.
- **A4** establishes a *new* universal fact `∀x :: P(x)` from available ground
  evidence — the direction is ground → ∀.

In A2, the `assert P(e)` is the trigger; the universal is already in scope. In A4,
the `assert forall x :: P(x)` is the goal; the ground facts are already in scope.
