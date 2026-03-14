# Problem 5: Euclidean GCD on Bitvectors - Hints

## Why Z3 fails
Two fundamental issues:
1. **Theory bridging**: The spec uses `Gcd` on `nat`, but the implementation uses `bv8` subtraction. Z3's bitvector theory and integer/nat theory don't automatically share facts about when `(a - b) as int == a as int - b as int`.
2. **Recursive explosion**: The `Gcd` function is recursive, and Z3 unfolds it aggressively when checking the loop invariant, leading to resource exhaustion. With bv8 values up to 255, Z3 may try to unfold hundreds of Gcd steps.

## Key insight
Make `Gcd` **opaque** with `{:opaque}` to prevent uncontrolled unfolding, and provide explicit one-step unfolding lemmas. Also provide a lemma proving bitvector subtraction matches integer subtraction when there's no underflow.

## Proof strategy
1. **`{:opaque}` on Gcd**: Prevents Z3 from unfolding the recursive definition. Each unfolding must be explicitly requested via `reveal Gcd()`.
2. **Controlled unfolding lemmas**:
   - `GcdZeroLeft(b)`: ensures `Gcd(0, b) == b`
   - `GcdZeroRight(a)`: ensures `Gcd(a, 0) == a`
   - `GcdSubLeft(a, b)`: when `a >= b > 0`, ensures `Gcd(a, b) == Gcd(a-b, b)`
   - `GcdSubRight(a, b)`: when `0 < a < b`, ensures `Gcd(a, b) == Gcd(a, b-a)`
3. **BvSubAsInt lemma**: Proves `(a - b) as int == a as int - b as int` when `a >= b`. This bridges the bitvector and integer theories.
4. **Loop invariant**: `Gcd(a as int, b as int) == Gcd(a0 as int, b0 as int)`. Call the appropriate unfolding lemma and BvSubAsInt before each subtraction.
5. **After loop**: Call GcdZeroLeft or GcdZeroRight to resolve the final value.
