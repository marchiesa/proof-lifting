# Problem 8: Modular Arithmetic — Modular Sum

## Category
Modular / Non-linear Arithmetic

## What makes this hard
The postcondition `result == SumSeq(s) % m` and the loop body `result := (result + s[i]) % m` require Z3 to reason about the modular identity:
```
(a % m + b) % m == (a + b) % m
```

This identity ALWAYS times out in Z3 because:
1. The `%` operator's semantics involve integer division: `a % m == a - (a/m) * m`
2. This introduces non-linear terms `(a/m) * m`
3. Z3's NL solver cannot handle the interaction between division and multiplication

Even simpler identities fail:
- `(x + m) % m == x % m` — timeout
- `a >= m ==> a % m == (a - m) % m` — timeout

## The misleading error
```
a postcondition could not be proved on this return path
  ensures result == SumSeq(s) % m
```
An LLM will try to add `invariant result == SumSeq(s[..i]) % m`, which also times out.

## The fix
Three changes required:

1. **Change the postcondition** from `result == SumSeq(s) % m` to an existence-based formulation:
   ```dafny
   ensures result < m
   ensures exists k: nat :: result + k * m == SumSeq(s)
   ```

2. **Replace `%` in the loop body** with manual subtraction:
   ```dafny
   result := result + s[i];
   if result >= m { result := result - m; }
   ```

3. **Track a ghost counter** `k` that counts subtractions, with invariant `total == result + k * m`. Z3 handles `(k+1)*m == k*m + m` via simple distributivity, unlike the general modular identity.

This requires the `SumSeqStep` lemma for the recursive-function-over-slices issue (same as Problems 1/3) and `SumSeqNonneg` for positivity.
