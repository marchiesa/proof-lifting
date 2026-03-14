# Problem 6: Quantifier Alternation — Surjective Range Covering

## Category
Quantifier Alternation / Skolemization

## What makes this hard
The surjectivity precondition uses a forall-exists (ALL-EXISTS) pattern:
```
forall y :: 0 <= y < m ==> exists x :: 0 <= x < n && f[x] == y
```

Z3's quantifier instantiation is trigger-based. For `forall y :: P(y)`, Z3 picks a trigger pattern from P(y) and instantiates the quantifier whenever a matching term appears. But here, the only interesting term in the body is `f[x]`, which involves the existentially quantified `x`. Z3 would need to guess `x` before it can create a trigger — a chicken-and-egg problem.

This means:
- The precondition is NEVER instantiated by Z3
- No invariant can reference the surjectivity property usefully
- Even ghost helper functions that try to extract the witness fail

## The misleading error
Multiple errors including index out of range and postcondition failures. The LLM will try adding invariants, but no invariant formulation can work because the fundamental issue is that Z3 can't use the precondition.

## The fix
**Skolemize at the API level**: Change the method signature to accept a `ghost preimages: seq<int>` parameter that explicitly witnesses the existential. Instead of:
```
requires Surjective(f, n, m)  // forall y, exists x, f[x] == y
```
Use:
```
requires forall y :: 0 <= y < m ==> 0 <= preimages[y] < n && f[preimages[y]] == y
```

This converts the ALL-EXISTS into a simple ALL that Z3 handles easily. Then restructure the algorithm to iterate over outputs y (not inputs i) and use linear search bounded by the ghost witness for termination.
