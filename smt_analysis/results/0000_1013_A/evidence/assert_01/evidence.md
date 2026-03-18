# Evidence Bundle: assert a + b == a;
**Line 94**

## The Assertion
```dafny
assert a + b == a;
```

**SMT encoding:**
- LHS: `a + b` → `Seq#Append(a, b)`
- RHS: `a` → `a`

## What Breaks Without It
**Dafny error:** a postcondition could not be proved on this return path
**Related:** this is the postcondition that could not be proved
**Failing condition:** `invariant maintained: ySum == Sum(y[..i])` (invariant_maintained)

## Counterexample Model (spurious)
Z3 result: `unknown`

**Variable assignments:**
```
  Seq#Empty = T@Seq!val!0
  a#0 = T@Seq!val!1
  b##1_0@0 = T@Seq!val!2
  b#0 = T@Seq!val!0
  s##1_0@0 = T@Seq!val!2
  v##1_0@0 = 0
```

**Sequence lengths:**
```
  |Seq#Empty| = 0
  |T@Seq!val!3| = 611
  |T@Seq!val!4| = 611
  |a#0| = 612
  |s##1_0@0| = 612
```

**Seq#Take interpretation:**
```
  Seq#Take(s##1_0@0 611) = T@Seq!val!3
  Seq#Take(a#0 611) = T@Seq!val!4
  Seq#Take(T@Seq!val!3 610) = T@Seq!val!5
  Seq#Take(T@Seq!val!4 610) = T@Seq!val!6
```

**Sum interpretation:**
```
  s##1_0@0 -> 489
  a#0 -> 8855
  Seq#Empty -> 0
  s##1_0@0 -> 489
  T@Seq!val!3 -> (- 8366)
  Seq#Empty -> 0
  a#0 -> 8855
  T@Seq!val!4 -> 0
  s##1_0@0 -> 489
  T@Seq!val!3 -> (- 8366)
  Seq#Empty -> 0
  a#0 -> 8855
  T@Seq!val!4 -> 0
  T@Seq!val!5 -> 0
  T@Seq!val!6 -> 8366
```

## Relevant Axioms (1 found)

These are all axioms in the SMT preamble whose primary trigger
pattern involves the same operations as the assertion:

### Axiom 1
- **Trigger:** `Seq#Equal _seq_ _seq_`
- **QID:** `outputbpl.2473:15`

## Trigger Gap Analysis (heuristic)
**Pattern:** `empty_concat_identity`
**Description:** The solver knows |b|==0 from the branch condition but does not conclude b==Seq#Empty(). The axiom Seq#Append(s, Seq#Empty())==s requires the second argument to literally be Seq#Empty(), not just a sequence with length 0. The solver cannot bridge the gap between Seq#Length(b)==0 and b==Seq#Empty().
**Needed:** `Seq#Append(a, b) == a`
**Missing:** `Seq#Append(s, b) where Seq#Length(b)==0 → s`

## Diagnosis Question

Given the axioms above, explain precisely why the Z3 solver
cannot derive `a + b == a` on its own.
What specific axiom or trigger pattern is missing from the
SMT encoding that would allow the solver to derive this equality?
Is this a fundamental limitation of the axiomatization, or a
trigger/e-matching gap that could be fixed?