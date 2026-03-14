# Problem 7: Decreases Clause Tricks — Two-Pointer Convergence

## Category
Decreases Clause / Loop Invariant Interaction

## What makes this hard
The loop checks three elements per iteration (s[lo], s[hi], s[lo+1]) and advances lo by 2 and hi by 1. The invariants are obvious:
```
forall k :: 0 <= k < lo ==> s[k] != target
forall k :: hi < k < |s| ==> s[k] != target
```

The trap: advancing `lo` by 2 means the invariant `forall k :: 0 <= k < lo` must cover the element at `lo+1` as well. When `lo + 1 >= hi`, there is no room to check `s[lo+1]` before the conditional, so jumping `lo := lo + 2` would skip an unchecked element, violating the invariant.

The termination argument is `decreases hi - lo`, which works because the gap shrinks by 3 each iteration (lo+2, hi-1). But this requires that we only advance when `lo + 1 < hi`, otherwise the gap is too small for a full step.

## The misleading error
```
this invariant could not be proved to be maintained by the loop
  invariant 0 <= lo <= |s|
```
This looks like a simple bounds error, but the real issue is that without the `lo + 1 >= hi` guard, the advance can violate the checked-elements invariant.

## The fix
Add `if lo + 1 >= hi { return; }` after checking s[lo], s[hi], and s[lo+1]. This ensures:
1. All remaining elements have been checked before returning
2. The `lo := lo + 2` only executes when there's enough gap
3. `decreases hi - lo` is strictly decreasing when we don't return early
