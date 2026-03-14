# Problem 1: Fuel Trap — Recursive Flatten Length

## Category
Fuel Trap

## What makes this hard
The recursive functions `FlatLen` and `Flatten` are defined by peeling off the **first** element (`ss[0]`) and recursing on `ss[1..]`. But the loop processes elements left-to-right using a slice `ss[..i]` that **grows from the right**.

The obvious invariants are:
```
invariant total == FlatLen(ss[..i])
invariant total == |Flatten(ss[..i])|
```

These are logically correct but Dafny cannot verify the inductive step. To prove maintenance, Dafny would need to show:
```
FlatLen(ss[..i+1]) == FlatLen(ss[..i]) + |ss[i]|
```

This requires fully unrolling the recursion from index 0 through i+1, which exceeds Dafny's default fuel. The recursion peels from the left but the change happens on the right — Dafny can't "see through" the recursion to relate `ss[..i+1]` to `ss[..i]`.

## The misleading error
```
this invariant could not be proved to be maintained by the loop
```
This suggests the invariant is wrong, but it's actually correct — the SMT solver just can't verify the inductive step.

## The fix
Write explicit inductive lemmas (`FlatLenStep`, `FlattenStep`) that prove the step property by structural induction, bridging the recursion direction mismatch. Call these lemmas inside the loop body before the update.
