# Problem 3: Sequence Slicing Pitfalls — Merge Sorted Halves

## Category
Sequence Slicing / Trigger Gap

## What makes this hard
The merge is standard and the invariants are textbook:
- `SortedSeq(result)` — result built so far is sorted
- `result[|result|-1] <= a[i]` / `<= b[j]` — tail of result <= next candidates
- `multiset(result) == multiset(a[..i]) + multiset(b[..j])` — element preservation

The multiset invariant is the trap. When we append `a[i]` and increment `i`, Z3 needs:
```
multiset(a[..i+1]) == multiset(a[..i]) + multiset{a[i]}
```
This follows from `a[..i+1] == a[..i] + [a[i]]`, which is trivially true but Z3 cannot derive it automatically. The sequence slicing axioms in Z3 don't generate this decomposition without an explicit trigger.

## The misleading error
```
this invariant could not be proved to be maintained by the loop
```
Points at the multiset invariant, suggesting the invariant is wrong.

## The fix
Three assertion pairs:
1. `assert a[..i+1] == a[..i] + [a[i]];` in the if-branch
2. `assert b[..j+1] == b[..j] + [b[j]];` in the else-branch
3. `assert a[..|a|] == a;` and `assert b[..|b|] == b;` after the loop

These create the terms Z3 needs to trigger multiset concatenation axioms. Also needs `decreases |a| - i + |b| - j` for termination.
