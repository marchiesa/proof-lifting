# Problem 5: Map/Set Reasoning Gaps — Histogram

## Category
Map/Set Reasoning + Fuel Trap

## What makes this hard
This problem combines three SMT difficulties:

1. **Recursive function over slices**: `CountIn(s[..i], x)` can't be stepped to `CountIn(s[..i+1], x)` without a lemma (same pattern as Problem 1/3)

2. **Map domain reasoning**: After `hist[key := val]`, Z3 knows `key in hist` but struggles to prove the preservation of the domain invariant `forall x :: x in hist <==> x in s[..i+1]` without explicit help.

3. **Negative reasoning about maps**: When `key !in hist`, we need `CountIn(s[..i], key) == 0`. This follows from `key !in s[..i]`, but Z3 can't derive this from the recursive definition of `CountIn` without an explicit lemma (`CountInZero`).

The invariants are textbook:
```dafny
forall x :: x in hist <==> x in s[..i]
forall x :: x in hist ==> hist[x] == CountIn(s[..i], x)
```

## The misleading error
Points at the count invariant, suggesting it's wrong.

## The fix
- `CountInStep` lemma: proves `CountIn(s[..i+1], x) == CountIn(s[..i], x) + ...`
- `CountInZero` lemma: proves `x !in s ==> CountIn(s, x) == 0`
- Explicit `forall` proof blocks inside the loop for both branches
- `assert s[..i+1] == s[..i] + [s[i]]` for domain reasoning
- `assert s[..|s|] == s` after the loop
