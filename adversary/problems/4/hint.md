# Problem 4: Non-linear Arithmetic — Power of Two Bound

## Category
Non-linear Arithmetic (NL)

## What makes this hard
The recursive function `Pow2(n)` is straightforward, and the loop invariant `result == Pow2(i)` is obvious. But Z3 cannot prove basic properties about `Pow2` from its recursive definition:

1. **Pow2(n) >= 1** — requires induction, not just NL
2. **Pow2(n) % 2 == 0** for n > 0 — requires NL reasoning about `2 * Pow2(n-1)`
3. **Pow2(a) * Pow2(b) == Pow2(a+b)** — requires both induction and NL

Z3's NL solver is fundamentally limited: it can handle some quadratic constraints but not general inductive arguments about recursive functions involving multiplication.

## The misleading error
```
a postcondition could not be proved on this return path
  ensures result >= 1
```
This seems absurd — we're computing a power of 2! The result is obviously >= 1. An LLM will likely try adding the invariant `result >= 1`, which also fails because Z3 needs to know `Pow2(i) >= 1` to prove it, which is the same problem.

## The fix
Write explicit inductive lemmas:
- `Pow2Positive(n)` proving `Pow2(n) >= 1` by induction
- `Pow2Even(n)` proving `Pow2(n) % 2 == 0` for n > 0
- `Pow2Add(a, b)` proving `Pow2(a) * Pow2(b) == Pow2(a+b)` by induction on a

Call these lemmas at the appropriate points. The `Pow2Add` lemma is particularly tricky because it needs explicit intermediate NL assertions to guide Z3 through the chain of equalities.
