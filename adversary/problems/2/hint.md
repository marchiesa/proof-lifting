# Problem 2: Missing Triggers — Partition Into Evens and Odds

## Category
Missing Triggers / Quantifier Instantiation

## What makes this hard
The multiset invariant `multiset(evens) + multiset(odds) == multiset(s[..i])` is logically correct, but Z3 cannot prove the inductive step. When `i` increments to `i+1`, Z3 needs to know:

```
multiset(s[..i+1]) == multiset(s[..i]) + multiset{s[i]}
```

This follows from the sequence identity `s[..i+1] == s[..i] + [s[i]]`, but Z3's multiset axioms are guarded by triggers that only fire when Z3 "sees" the connection between `s[..i+1]` and `s[..i] + [s[i]]`. Without an explicit assertion creating this term, the trigger never fires.

## The misleading error
```
this invariant could not be proved to be maintained by the loop
```
The invariant looks wrong, but it's actually correct. An LLM will likely try alternative invariant formulations rather than adding the trigger assertion.

## The fix
Add a single assertion inside the loop body:
```dafny
assert s[..i+1] == s[..i] + [s[i]];
```
This creates the terms that trigger Z3's multiset decomposition axioms. The invariant itself doesn't change — only the hint to Z3 changes.

Also need `assert s[..|s|] == s;` after the loop to connect the final slice to the full sequence.
