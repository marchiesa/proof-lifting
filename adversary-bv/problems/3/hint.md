# Problem 3: Bit Reversal - Hints

## Why Z3 fails
The loop builds the reversed value one bit at a time via `(r << 1) | (tmp & 1)`. The postcondition requires `forall i :: GetBit(r, i) == GetBit(x, 7-i)`. Z3 cannot reason about how shifting `r` left by 1 and OR-ing a bit affects ALL 8 bit positions simultaneously -- this requires combined quantifier instantiation and bitvector shift reasoning.

## Key insight
Define a ghost function `PartialRev(x, j)` that explicitly computes what the reversed value should be after `j` iterations. Since bv8 has only 8 bits, enumerate all 9 cases (j = 0 to 8) with explicit bit extraction and placement.

## Proof strategy
1. **Ghost function `PartialRev(x, j)`**: For each `j` from 0 to 8, define the value as OR of shifted `GetBit` calls. For example, `PartialRev(x, 3) = (GetBit(x, 0) << 2) | (GetBit(x, 1) << 1) | GetBit(x, 2)`.
2. **Step lemma**: Prove `(PartialRev(x, j) << 1) | GetBit(x, j) == PartialRev(x, j + 1)` for each `j`. Z3 can verify this since both sides are concrete bitvector expressions.
3. **Loop invariant**: `r == PartialRev(x, j)` and `tmp == x >> j`.
4. **Postcondition**: After the loop, `r == PartialRev(x, 8)`. Z3 can verify that `GetBit(PartialRev(x, 8), i) == GetBit(x, 7 - i)` by expanding the definition.
