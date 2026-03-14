# Problem 1: Popcount - Hints

## Why Z3 fails
The loop body uses `x & (x-1)` to clear the lowest set bit, but the postcondition requires matching a recursive spec `PopcountSpec` that peels off the LSB with `x >> 1`. Z3 cannot automatically connect these two different bit-manipulation strategies.

## Key insight
You need a lemma proving that `PopcountSpec(x & (x - 1)) == PopcountSpec(x) - 1` for any nonzero `x`. This lemma requires induction on the bitvector value.

## Proof strategy
1. **Loop invariant**: `count + PopcountSpec(tmp) == PopcountSpec(x)` - the count so far plus the remaining popcount equals the total.
2. **Lemma by case split on LSB**:
   - If `x & 1 == 1`: then `x & (x-1) == x - 1`, the LSB is cleared, and `(x-1) >> 1 == x >> 1`. This directly shows popcount decreases by 1.
   - If `x & 1 == 0`: recurse on `x >> 1`. The key identity is `(x & (x-1)) >> 1 == (x >> 1) & ((x >> 1) - 1)` - clearing the lowest set bit commutes with shifting out zero LSBs.
3. **Decreases**: Use `x as int` with the inductive lemma.
