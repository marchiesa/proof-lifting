# Problem 2: Power of 2 Check - Hints

## Why Z3 fails
The spec uses an existential quantifier: `exists k :: 0 <= k < 8 && x == 1 << k`. The implementation uses the bit trick `x != 0 && x & (x-1) == 0`. Z3 cannot:
1. Find a witness `k` for the existential when the bit trick holds
2. Prove the bit trick holds when given an existential witness

## Key insight
You need **two lemmas** (both directions of the equivalence) and a **trigger function** for the existential quantifier.

## Proof strategy
1. **Trigger function**: Define `Shift1Left(k: int): bv8` that computes `(1 as bv8) << (k as bv8)`. Use `{:trigger Shift1Left(k)}` on the existential to help Z3 instantiate it.
2. **Forward (bit trick => spec)**: Enumerate all 8 single-bit values (1, 2, 4, 8, 16, 32, 64, 128) via `if/else` chain. For each, assert `Shift1Left(k)` with the right `k` to provide the existential witness.
3. **Backward (spec => bit trick)**: Eliminate the existential with `:| ` and Z3 handles each concrete shift amount automatically.
4. **Method body**: Call the appropriate lemma in each branch (`result == true` vs `result == false`), using proof by contradiction for the false case.
