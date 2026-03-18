## Assertion: assert scores[1..i+1] == scores[1..i] + [scores[i]];

### Dafny → SMT translation
- LHS: `scores[1..i+1]` → `Seq#Drop(Seq#Take(scores, i+1), 1)`
- RHS: `scores[1..i] + [scores[i]]` → `Seq#Append(Seq#Drop(Seq#Take(scores, i), 1), Seq#Build(Seq#Empty(), $Box(Seq#Index(scores, i))))`

### Relevant axioms and triggers

1. **Seq#Take/Seq#Append split** (line ~22863):
   ```
   forall s0, s1, n. n == |s0| ==>
     Seq#Take(Seq#Append(s0, s1), n) == s0 AND
     Seq#Drop(Seq#Append(s0, s1), n) == s1
   ```
   Trigger: `{Seq#Take(Seq#Append(s0, s1), n)}` or `{Seq#Drop(Seq#Append(s0, s1), n)}`
   Works **opposite direction**: simplifies Take/Drop OF Append, cannot go from Drop-of-Take to Append form.

2. **Seq#Drop/Seq#Build commutativity** (line ~22730):
   ```
   forall s, x, n. 0 <= n <= |s| ==> Seq#Drop(Seq#Build(s, x), n) == Seq#Build(Seq#Drop(s, n), x)
   ```
   Trigger: `{Seq#Drop(Seq#Build(s, x), n)}`

3. **Seq#Index of Seq#Take** (line ~23137):
   ```
   forall s, n, j. 0 <= j < n AND j < |s| ==> Seq#Index(Seq#Take(s, n), j) == Seq#Index(s, j)
   ```

4. **Seq#Index of Seq#Drop** (line ~23493):
   ```
   forall s, n, j. 0 <= n AND 0 <= j < |s|-n ==> Seq#Index(Seq#Drop(s, n), j) == Seq#Index(s, j+n)
   ```

5. **Seq#Equal extensionality** (line ~23179):
   ```
   forall s0, s1. Seq#Equal(s0, s1) <==> (|s0| == |s1| AND forall j. 0<=j<|s0| ==> s0[j] == s1[j])
   ```
   Trigger: `{Seq#Equal(s0, s1)}`

### What the failing VC contains

In the WITHOUT-assertion VC:
- `Seq#Drop(Seq#Take(scores, i), 1)` — from assumed loop invariant (scores[1..i])
- `Seq#Drop(Seq#Take(scores, n), 1)` — from post-loop assertion (scores[1..n])
- `CountBetter(Seq#Drop(Seq#Take(scores, i), 1), myScore)` — from invariant
- `CountBetter(Seq#Append(Seq#Drop(Seq#Take(scores, i), 1), Seq#Build(Seq#Empty(), ...)), myScore)` — from CountBetterAppend postcondition

In the WITH-assertion VC (additionally):
- `Seq#Equal(Seq#Drop(Seq#Take(scores, i+1), 1), Seq#Append(Seq#Drop(Seq#Take(scores, i), 1), Seq#Build(Seq#Empty(), Seq#Index(scores, i))))`
  — this is the explicit assertion, checked and then assumed

### The gap

**Term generation gap.** The invariant maintenance check needs to prove:
```
rank' == 1 + CountBetter(scores[1..i+1], myScore)
```

The CountBetterAppend postcondition provides:
```
CountBetter(scores[1..i] + [scores[i]], myScore) == CountBetter(scores[1..i], myScore) + (if TotalScore(scores[i]) > myScore then 1 else 0)
```

To connect these, Z3 needs to know:
```
scores[1..i+1] == scores[1..i] + [scores[i]]
```
i.e., `Seq#Drop(Seq#Take(s, i+1), 1) == Seq#Append(Seq#Drop(Seq#Take(s, i), 1), Seq#Build(Seq#Empty(), Seq#Index(s, i)))`

Z3 cannot derive this because:
1. There is **no axiom** that relates `Seq#Drop(Seq#Take(s, hi), lo)` to an `Seq#Append` form.
2. The existing Take-of-Append axiom works in the **reverse direction** (simplifying Append → Take, not Take → Append).
3. The extensionality axiom (Seq#Equal) requires a `Seq#Equal` ground term to trigger, which doesn't exist without the assertion.
4. Even element-by-element comparison would require `Seq#Index(Seq#Drop(Seq#Take(s, i+1), 1), k)` terms for arbitrary `k`, which don't exist in the VC.

### Ghost variable test result
Ghost variable probe (introducing `ghost var lhs := scores[1..i+1]; ghost var rhs := scores[1..i] + [scores[i]];` without asserting equality) also fails. This confirms the solver needs the **explicit equality assertion**, not just the presence of both terms. The terms alone are insufficient because the Seq#Equal extensionality axiom requires a `Seq#Equal(lhs, rhs)` ground term to fire.

### Diagnosis
**Missing axiom: slice-append decomposition for Seq#Drop(Seq#Take(s, hi+1), lo).** There is no Boogie prelude axiom that relates `Seq#Drop(Seq#Take(s, hi+1), lo)` (a slice `s[lo..hi+1]`) to `Seq#Append(Seq#Drop(Seq#Take(s, hi), lo), Seq#Build(Seq#Empty(), Seq#Index(s, hi)))` (the slice `s[lo..hi] + [s[hi]]`). This is the sequence-theoretic identity `s[lo..hi+1] == s[lo..hi] + [s[hi]]`.
