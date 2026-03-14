# Problem 4: Count Leading Zeros - Hints

## Why Z3 fails
The loop scans bits from position 7 downward, counting zeros. The recursive spec `ClzSpec(x, pos)` counts from the top bit of a `pos`-wide window. Z3 cannot connect the loop's partial scan to the recursive spec because:
1. Quantifiers over bit positions with bitvector shifts lack good triggers
2. The recursive spec processes bits top-down, but Z3 needs to "skip" past multiple zeros at once

## Key insight
You need a "skip" lemma: if k consecutive bits are zero, then `ClzSpec(x, pos) == k + ClzSpec(x, pos - k)`. This lets you fast-forward the recursive spec past all the zeros the loop has seen.

## Proof strategy
1. **Trigger helper**: Define `GetBitAt(x, i)` as `(x >> (i as bv8)) & 1` to provide a trigger for quantifiers over bit positions.
2. **Loop invariants**:
   - `count == 7 - pos` (count tracks position)
   - `forall i {:trigger GetBitAt(x, i)} :: pos < i <= 7 ==> GetBitAt(x, i) == 0` (all scanned bits are zero)
3. **ClzSkip lemma**: If bits from `pos-k` to `pos-1` are all zero, then `ClzSpec(x, pos) == k + ClzSpec(x, pos-k)`. Prove by induction on `k`.
4. **ClzHit lemma**: If bit `pos-1` is 1, then `ClzSpec(x, pos) == 0`. Trivial from definition.
5. **After loop**: Apply ClzSkip with `k = 7 - pos` zeros, then ClzHit if a 1-bit was found, or ClzSkip with `k = 8` if all bits are zero.
