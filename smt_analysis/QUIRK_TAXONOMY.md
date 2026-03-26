# SMT Quirk Taxonomy

## High-Level Categories

### A. E-matching (78 assertions, 43%)

The solver's pattern-based quantifier instantiation (e-matching) does not
fire because the required ground term is absent from the e-graph. The axiom
or definition exists, but e-matching is purely reactive — it only instantiates
when a matching term already appears. The programmer must inject the term.

This covers:
- Existentials that need a witness term
- Predicates/functions that need to be evaluated at specific arguments
- Universal quantifiers that need to be instantiated at a specific value
- Length facts behind uninstantiated quantifiers

### B. Missing axioms (52 assertions, 29%)

The solver's theory lacks a direct axiom for the needed fact. The fact is
derivable in principle (e.g., through sequence extensionality: same length +
same elements at every index → equal), but the derivation requires reasoning
that e-matching cannot perform (typically a nested universal quantifier).

The key distinction from category A: in A, the axiom/definition exists and
adding a ground term causes it to fire. In B, no single axiom states the
needed equality — a new axiom would need to be added to the theory.

All instances in our dataset involve sequence object-level equalities.
Z3's sequence theory axiomatizes sequences through element-level properties
(length, index access) but lacks direct axioms asserting when two
differently-constructed sequence expressions are equal objects.

### C. Theory incompleteness (10 assertions, 5%)

The built-in decision procedure is fundamentally incomplete for the class
of problems. Nonlinear integer arithmetic (NLA) is undecidable in general,
and Z3's NLA solver is incomplete. No trigger engineering or assertion
placement can fix this — the solver needs algebraic hints.

### D. Propagation failure (42 assertions, 23%)

All individual facts are already present as ground terms in the solver's
knowledge (e-graph, asserted equalities, known bounds). No quantifiers need
to be instantiated, no axioms are missing. The solver simply does not chain
the known facts together to reach the conclusion.

Note: some of these may turn out to be e-matching issues in disguise upon
closer inspection (e.g., an equality that's behind an uninstantiated
quantifier). We err on the propagation side when the mechanism is unclear.

---

## Detailed Quirk Types

### A1. existential-witness (23 assertions, 10 problems)

**High-level:** A. E-matching
**Mechanism:** The postcondition contains an `exists` quantifier. To prove it,
Z3 needs a ground term in the e-graph that serves as the witness. No such
term exists — the solver would need to "invent" or enumerate candidates, but
e-matching is purely reactive.

This is the `Scary` example:
```dafny
method Scary(s: seq<int>)
  requires |s| > 10
{
  assert exists k :: 0 <= k < |s| && s[k] == s[k];  // FAILS — no ground term for k
}
```
Adding `var _ := s[0];` fixes it by putting `s[0]` into the e-graph.

**Sub-patterns:**

| Pattern | Count | Example |
|---------|-------|---------|
| Function equality providing witness | 12 | `assert FriendSum(a1,a2,a3,a4, T,T,F,F) == FriendSum(a1,a2,a3,a4, F,F,T,T);` |
| Predicate evaluation providing witness | 6 | `assert IsValidSolution(x, y, z, a, b, c);` |
| Explicit existential witness | 5 | `assert exists c \| left <= c < right :: grid[top][c] == '*';` |

**Representative example (0053_1230_A):**
```dafny
ghost predicate CanDistributeEqually(a1: int, a2: int, a3: int, a4: int) {
  exists b1, b2, b3, b4 ::
    FriendSum(a1,a2,a3,a4, b1,b2,b3,b4) == FriendSum(a1,a2,a3,a4, !b1,!b2,!b3,!b4)
}

method DawidAndCandies(...) returns (result: bool)
  ensures result == CanDistributeEqually(a1, a2, a3, a4)
{
  result := (a1+a2 == a3+a4) || ...;
  if result {
    if a1 + a2 == a3 + a4 {
      // Provides witness: b1=T, b2=T, b3=F, b4=F
      assert FriendSum(a1,a2,a3,a4, true,true,false,false) ==
             FriendSum(a1,a2,a3,a4, false,false,true,true);  // <-- essential
    }
  }
}
```

---

### A2. predicate-instantiation (22 assertions, 10 problems)

**High-level:** A. E-matching
**Mechanism:** A predicate is defined and all argument values are known, but
Z3 doesn't evaluate (unfold) the predicate at those specific arguments. The
predicate definition is a quantified axiom with a trigger on the predicate
symbol, but the trigger doesn't fire in the current context.

Unlike existential-witness (A1), these assertions don't provide a witness for
an `exists`. They force the solver to evaluate a predicate to make its result
available in the proof context.

| Problem | Predicate | Count |
|---------|-----------|-------|
| 0003_1028_A | CellInSquare, IsBlackSquareCenteredAt | 4 |
| 0015_1064_A | IsTriangle | 4 |
| 0073_1206_A | InSeq | 5 |
| 0041_1143_A | CanExitAfter | 1 |
| 0095_1301_A | HasValidSwapAtPos | 1 |
| 0097_1311_A | ValidStep | 1 |
| 0110_1325_B | Sorted | 1 |
| 0126_14_A | ContainsAllShaded, TightBounds, IsMinimalBoundingBox | 3 |
| 0142_1360_A | IsMinimalSide | 2 |

**Representative example (0015_1064_A):**
```dafny
ghost predicate IsTriangle(a: int, b: int, c: int) {
  a + b > c && a + c > b && b + c > a
}

// In a branch where m == a:
assert IsTriangle(a + 0, b + minutes, c + (minutes - 0 - minutes));  // <-- essential
// Z3 has a, b, c, minutes but won't unfold IsTriangle at these args
```

---

### A3. function-unfolding (12 assertions, 6 problems)

**High-level:** A. E-matching
**Mechanism:** A function is defined and arguments are known, but Z3 doesn't
evaluate the function at those arguments. Similar to A2 but for functions
returning values (not predicates returning bool), and the result needs to
equal some known value.

| Problem | Function | Count |
|---------|----------|-------|
| 0028_1038_A | CountChar, CountIth | 4 |
| 0027_1092_A | CountChar, ExactCount | 2 |
| 0061_1191_A | CategoryRank | 1 |
| 0083_1194_A | InitialList, FinalList, EvenList | 3 |
| 0110_1325_B | CountDupsInSorted | 1 |
| 0121_1370_A | Gcd | 1 |

**Representative example (0121_1370_A):**
```dafny
ghost function Gcd(a: int, b: int): int
  requires a > 0 && b > 0
  decreases b
{ if a % b == 0 then b else Gcd(b, a % b) }

// Solver knows wb % wa == 0 but doesn't unfold Gcd to reach the base case
assert Gcd(wb, wa) == wa;  // <-- essential
assert Gcd(wa, wb) == wa;  // <-- essential
```

---

### A4. quantifier-instantiation (12 assertions, 9 problems)

**High-level:** A. E-matching
**Mechanism:** A `forall` is available (from an invariant, precondition, or
prior assertion) but Z3 doesn't instantiate it at the specific value needed
for the current proof obligation.

**Representative examples:**
```dafny
// 0035_1162_A: after loop maintaining forall j | 0 <= j < i :: ans[j] == EffectiveCap(j, ...)
// After loop exit (i == n), need forall j | 0 <= j < n :: ...
// Solver doesn't reconnect the loop invariant to the postcondition
assert forall j | 0 <= j < n :: ans[j] == EffectiveCap(j, h, restrictions);  // <-- essential

// 0077_1244_A: need to show no other assignment works
assert forall x0, y0 {:trigger ValidAssignment(x0, y0, a, b, c, d, k)}
  :: !ValidAssignment(x0, y0, a, b, c, d, k);  // <-- essential
```

---

### A5. length-tracking (9 assertions, 3 problems)

**High-level:** A. E-matching
**Mechanism:** Sequence length is determined by construction or an invariant
(e.g., `forall r :: |grid[r]| == m`), but Z3 doesn't instantiate the length
fact at the specific index needed.

**Representative examples:**
```dafny
// 0126_14_A: invariant says all rows have length m
// Solver doesn't instantiate at r = top
assert |grid[top]| == m;  // <-- essential

// 0028_1038_A: sequence built with known length
assert |upper| == k;      // <-- essential
assert |counts| == k;     // <-- essential
```

---

### B1. seq-extensionality (52 assertions, 25 problems)

**High-level:** B. Missing axioms
**Mechanism:** Z3's sequence theory axiomatizes sequences through element-level
properties (length, element access) but lacks direct object-level equality
axioms for common sequence compositions.

For example, there is no axiom stating:
```
Seq#Take(s, i+1) == Seq#Append(Seq#Take(s, i), Seq#Build(Seq#Index(s, i)))
```

A sequence extensionality axiom exists (two sequences with the same length
and the same elements at every index are equal), but it contains a nested
universal quantifier over indices that e-matching cannot instantiate. The
result is that the solver can verify element-level properties but cannot
conclude that two sequence expressions denote the same object.

**Sub-patterns:**

| Pattern | Count | Example |
|---------|-------|---------|
| take-full: `a[..\|a\|] == a` | 20 | `assert s[..\|s\|] == s;` |
| take-append: `a[..i+1] == a[..i] + [a[i]]` | 10 | `assert x[..i + 1] == x[..i] + [x[i]];` |
| take-of-take: `a[..i+1][..i] == a[..i]` | 8 | `assert a[..i + 1][..i] == a[..i];` |
| take-append (reversed) | 5 | `assert a[..i] + [a[i]] == a[..i + 1];` |
| take-self: `a[..n] == a` (where `n==\|a\|`) | 4 | `assert doors[..n] == doors;` |
| multiset equality | 3 | `assert multiset(arr[..]) == multiset(a);` |
| split-concat: `a == a[..i] + a[i..]` | 2 | `assert chapters == chapters[..i] + chapters[i..];` |

Adding dedicated axioms for the three most common sub-patterns (take-full,
take-append, take-of-take) would eliminate 38 of 52 B1 assertions (73%).

**SMT model evidence:** 18 assertions have confirmed Seq#Take != Seq#Append
in the Z3 counterexample model. 29 of 30 pattern-matched assertions also
have model evidence (model extracted with seq operations present).

**Representative example (0000_1013_A):**
```dafny
while i < |x|
  invariant 0 <= i <= |x|
  invariant result == F(x[..i], y[..i])
{
  assert x[..i + 1] == x[..i] + [x[i]];  // <-- essential
  assert x[..|x|] == x;                    // <-- essential
  i := i + 1;
}
```

---

### C1. nonlinear-arithmetic (10 assertions, 4 problems)

**High-level:** C. Theory incompleteness
**Mechanism:** Z3's nonlinear integer arithmetic (NLA) solver is incomplete.
Relationships between multiplication, division, and modulo require explicit
algebraic hints. NLA is undecidable in general.

| Sub-pattern | Count | Example |
|-------------|-------|---------|
| mod/div relationship | 6 | `assert r - shares * minS == r % minS;` |
| multiplication bounds | 3 | `assert shares * minS <= r;` |
| mod bounds | 1 | `assert 0 <= m % k < k;` |

**Representative example (0037_1150_A):**
```dafny
// Solver cannot connect multiplication to modulo
assert r - shares * minS == r % minS;       // <-- essential
assert shares * (maxB - minS) <= 0;          // <-- essential
```

---

### D1. equality-propagation (14 assertions, 7 problems)

**High-level:** D. Propagation failure
**Mechanism:** The solver has equalities between variables (from assignments
or prior assertions) but doesn't propagate them through to where they're
needed. The individual equalities are known; combining them is the problem.

Most are in 0003_1028_A (8 of 14), a complex geometry proof with many
intermediate variables.

**Representative examples:**
```dafny
// 0003_1028_A: variables computed from grid center coordinates
assert ly == gcr - ghalf;          // <-- essential
assert ry == gcr + ghalf + 1;      // <-- essential
assert ly + ry == 2 * gcr + 1;     // <-- essential (follows from above two!)
assert r - 1 == gcr;               // <-- essential
```

---

### D2. arithmetic-bounds (13 assertions, 7 problems)

**High-level:** D. Propagation failure
**Mechanism:** The solver has individual bound constraints but doesn't combine
them to derive the needed bound. Each inequality is known; the chain of
reasoning is not followed.

**Representative examples:**
```dafny
// 0003_1028_A: bounds from loop invariants not propagated
assert 1 <= r <= n;                // <-- essential
assert 1 <= c <= m;                // <-- essential

// 0015_1064_A: triangle inequality from sorted sides
assert a + b + c > 2 * m;         // <-- essential
assert minutes >= 0;               // <-- essential
```

---

### D3. indexing (9 assertions, 5 problems)

**High-level:** D. Propagation failure
**Mechanism:** The solver knows the value at a specific index (from a prior
assignment or loop body) but can't connect it across contexts — typically
across loop iterations, array updates, or frame conditions.

**Representative examples:**
```dafny
// 0003_1028_A: grid value known from loop condition/body
assert grid[ly][lx] == 'W';       // <-- essential
assert grid[ly][rx] == 'B';       // <-- essential

// 0036_1015_A: array frame condition — element unchanged by update elsewhere
assert A[p] == A_before[p];       // <-- essential
```

---

### D4. case-exhaustiveness (6 assertions, 1 problem)

**High-level:** D. Propagation failure
**Mechanism:** After a sequence of case-splitting assertions, the solver can't
derive that the current branch is unreachable (i.e., derive `false` from
contradictory facts). All in 0003_1028_A.

**Representative example:**
```dafny
// After establishing !CellInSquare(ry, j, gcr, gcc, ghalf)
// and deriving grid[ry][j] != 'B'
// the branch should be unreachable:
assert false;  // <-- essential (solver can't derive contradiction)
```

---

## Summary Table

| High-level | Low-level | Assertions | Problems | % |
|------------|-----------|------------|----------|---|
| **A. E-matching** | A1. existential-witness | 23 | 10 | 12.6% |
| | A2. predicate-instantiation | 22 | 10 | 12.1% |
| | A3. function-unfolding | 12 | 6 | 6.6% |
| | A4. quantifier-instantiation | 12 | 9 | 6.6% |
| | A5. length-tracking | 9 | 3 | 4.9% |
| | **A total** | **78** | | **42.9%** |
| **B. Missing axioms** | B1. seq-extensionality | 52 | 25 | 28.6% |
| | **B total** | **52** | | **28.6%** |
| **C. Theory incompleteness** | C1. nonlinear-arithmetic | 10 | 4 | 5.5% |
| | **C total** | **10** | | **5.5%** |
| **D. Propagation** | D1. equality-propagation | 14 | 7 | 7.7% |
| | D2. arithmetic-bounds | 13 | 7 | 7.1% |
| | D3. indexing | 9 | 5 | 4.9% |
| | D4. case-exhaustiveness | 6 | 1 | 3.3% |
| | **D total** | **42** | | **23.1%** |
| **Total** | | **182** | **52** | |

## Methodology

- **Source:** 104 verified Dafny programs from the dataset (108 verified, 4 timed out)
- **Assertion extraction:** AST mapping (`--ast-mapping`) to find `assert` statements
  in method bodies only (no lemma bodies, no invariants)
- **Ablation:** Remove one assertion at a time, run `dafny verify` with 30s timeout.
  Essential = verification fails without it.
- **De-duplication:** Same (problem, line, text) counted once
- **Model evidence:** For essential equality assertions, ran Dafny->Boogie with
  `/printModel:1` to extract Z3 counterexample. 18 assertions have confirmed
  Seq#Take != Seq#Append in the model.
- **Classification:** Regex pattern matching on assertion text + model-based
  diagnosis. High-level categorization by underlying SMT mechanism.
