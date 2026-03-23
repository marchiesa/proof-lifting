# SMT Quirk Classification

## Dataset Summary
- Total problems: 2
- Solved: 2
- With diagnosed quirks: 2
- Total quirks to classify: 11

## All Diagnosed Quirks

### Quirk 1 (from 0006_1017_A)
**Assertion:** `invariant 1 <= i <= n`
**Type:** invariant
**Mechanism:** structural_requirement
**Explanation:** Bounds invariant is structurally required. Without it, Z3 cannot prove that sequence slice indices (1 and i) are within bounds for Seq#Take and Seq#Drop operations. Also needed to establish CountBetter's forall precondition (elements have length >= 4) over the sub-slice scores[1..i].
**Ghost var test:** 
**Confidence:** high
**Without it:** {
  "result": "error",
  "failing_vc": "multiple",
  "dafny_error": "function precondition could not be proved; upper bound below lower bound or above length of sequence"
}

### Quirk 2 (from 0006_1017_A)
**Assertion:** `invariant rank == 1 + CountBetter(scores[1..i], myScore)`
**Type:** invariant
**Mechanism:** structural_requirement
**Explanation:** Accumulator invariant is structurally required. It connects the loop computation (rank) with the recursive ghost function (CountBetter). Without it, Z3 has no inductive hypothesis linking rank to the spec.
**Ghost var test:** 
**Confidence:** high
**Without it:** {
  "result": "error",
  "failing_vc": "postcondition",
  "dafny_error": "a postcondition could not be proved on this return path: ensures rank == ExpectedRank(n, scores)"
}

### Quirk 3 (from 0006_1017_A)
**Assertion:** `assert scores[1..i+1] == scores[1..i] + [scores[i]]`
**Type:** assertion
**Mechanism:** missing_take_drop_commutation_and_take_of_take_axioms
**Explanation:** When CountBetter unfolds on scores[1..i_new] (where i_new = old_i+1), it produces Seq#Take(Seq#Drop(Seq#Take(scores, i_new), 1), len-1) which Z3 must simplify to Seq#Drop(Seq#Take(scores, i_old), 1) (i.e., scores[1..i_old]). This requires (1) Take-Drop commutation: Seq#Take(Seq#Drop(s,k),n) == Seq#Drop(Seq#Take(s,n+k),k), and (2) Take-of-Take: Seq#Take(Seq#Take(s,m),n) == Seq#Take(s,n) when n<=m. Neither axiom exists in Boogie's prelude. The assertion provides the equality via Seq#Equal extensionality as a workaround.
**Ghost var test:** failed
**Confidence:** high
**Without it:** {
  "result": "error",
  "failing_vc": "invariant_maintained",
  "dafny_error": "this invariant could not be proved to be maintained by the loop: invariant rank == 1 + CountBetter(scores[1..i], myScore)"
}

### Quirk 4 (from 0009_1041_A)
**Assertion:** `invariant 1 <= i <= |a|`
**Type:** invariant
**Mechanism:** standard loop bounds invariant
**Explanation:** Without bounds on i, Z3 cannot prove that a[..i] is well-formed (requires 0 <= i <= |a|) or that SeqMin(a[..i]) is well-defined (requires |a[..i]| > 0).
**Ghost var test:** n/a
**Confidence:** high
**Without it:** {
  "result": "error",
  "failing_vc": "multiple",
  "dafny_error": "function precondition could not be proved (SeqMin requires |a|>0); upper bound below lower bound on a[..i]; FeasibilityLemma preconditions"
}

### Quirk 5 (from 0009_1041_A)
**Assertion:** `invariant lo == SeqMin(a[..i])`
**Type:** invariant
**Mechanism:** standard accumulator invariant
**Explanation:** Without tracking that lo == SeqMin of the prefix, there is no connection between the loop variable lo and the spec function SeqMin.
**Ghost var test:** n/a
**Confidence:** high
**Without it:** {
  "result": "error",
  "failing_vc": "postcondition",
  "dafny_error": "FeasibilityLemma precondition: lo == SeqMin(a) could not be proved"
}

### Quirk 6 (from 0009_1041_A)
**Assertion:** `invariant hi == SeqMax(a[..i])`
**Type:** invariant
**Mechanism:** standard accumulator invariant
**Explanation:** Without tracking that hi == SeqMax of the prefix, there is no connection between the loop variable hi and the spec function SeqMax.
**Ghost var test:** n/a
**Confidence:** high
**Without it:** {
  "result": "error",
  "failing_vc": "postcondition",
  "dafny_error": "FeasibilityLemma precondition: hi == SeqMax(a) could not be proved"
}

### Quirk 7 (from 0009_1041_A)
**Assertion:** `assert a[..i+1][..i] == a[..i];`
**Type:** assertion
**Mechanism:** missing Take-of-Take axiom
**Explanation:** SeqMin/SeqMax unfold recursively on a[..i+1], producing SeqMin(a[..i+1][..|a[..i+1]|-1]) = SeqMin(Seq#Take(Seq#Take(a, i+1), i)). To connect this to the old invariant SeqMin(Seq#Take(a, i)), Z3 must prove Seq#Take(Seq#Take(a, i+1), i) == Seq#Take(a, i). No axiom exists for this simplification, despite the parallel Drop-of-Drop axiom existing.
**Ghost var test:** failed
**Confidence:** high
**Without it:** {
  "result": "error",
  "failing_vc": "invariant_maintained",
  "dafny_error": "invariant lo == SeqMin(a[..i]) could not be proved to be maintained by the loop; invariant hi == SeqMax(a[..i]) could not be proved to be maintained by the loop"
}

### Quirk 8 (from 0009_1041_A)
**Assertion:** `assert a[..|a|] == a;`
**Type:** assertion
**Mechanism:** missing Take-of-full-length axiom
**Explanation:** After loop exit with i == |a|, invariants give lo == SeqMin(a[..|a|]) and hi == SeqMax(a[..|a|]). FeasibilityLemma requires lo == SeqMin(a). Z3 cannot prove SeqMin(Seq#Take(a, Seq#Length(a))) == SeqMin(a) because there is no axiom stating Seq#Take(s, Seq#Length(s)) == s. The parallel Drop(s, 0) == s axiom does exist.
**Ghost var test:** failed
**Confidence:** high
**Without it:** {
  "result": "error",
  "failing_vc": "postcondition",
  "dafny_error": "FeasibilityLemma preconditions: lo == SeqMin(a) and hi == SeqMax(a) could not be proved"
}

### Quirk 9 (from 0009_1041_A)
**Assertion:** `FeasibilityLemma(a, lo, hi, 0);`
**Type:** lemma_call
**Mechanism:** existential witness needed
**Explanation:** FeasibleStolenCount requires proving an existential (exists x :: ValidStoreConfig(a, x, |a|+k)). Z3 cannot find the witness x = SeqMin(a) without the lemma explicitly constructing it. The lemma calls SeqMinIsMin to prove all elements are >= lo, then asserts ValidStoreConfig(a, lo, |a|+k) to provide the witness.
**Ghost var test:** n/a
**Confidence:** high
**Without it:** {
  "result": "error",
  "failing_vc": "postcondition",
  "dafny_error": "postcondition MinStolenCount(a, stolen) could not be proved on return 0 path; FeasibleStolenCount not established (exists x :: ValidStoreConfig)"
}

### Quirk 10 (from 0009_1041_A)
**Assertion:** `FeasibilityLemma(a, lo, hi, res);`
**Type:** lemma_call
**Mechanism:** existential witness needed
**Explanation:** Same mechanism as call_feasibility_0 — needs explicit witness construction for the existential in FeasibleStolenCount.
**Ghost var test:** n/a
**Confidence:** high
**Without it:** {
  "result": "error",
  "failing_vc": "postcondition",
  "dafny_error": "postcondition MinStolenCount(a, stolen) could not be proved on return res path; FeasibleStolenCount not established"
}

### Quirk 11 (from 0009_1041_A)
**Assertion:** `InfeasibilityLemma(a, res - 1);`
**Type:** lemma_call
**Mechanism:** universal quantifier proof needed
**Explanation:** MinStolenCount requires proving !FeasibleStolenCount(a, res-1), which means proving (forall x :: !ValidStoreConfig(a, x, |a|+res-1)). This requires a proof by contradiction for each x, using witnesses from SeqMinInSeq and SeqMaxInSeq to derive contradictions. Z3 cannot construct this argument without the lemma.
**Ghost var test:** n/a
**Confidence:** high
**Without it:** {
  "result": "error",
  "failing_vc": "postcondition",
  "dafny_error": "postcondition MinStolenCount(a, stolen) could not be proved; !FeasibleStolenCount(a, k-1) not established"
}


## Unsolved Problems
None

## Your Task

Analyze ALL 11 quirks above. For each one, you have the assertion that was
needed, what happens without it, and a per-problem diagnosis.

1. **Group these into categories by UNDERLYING MECHANISM** (not by surface syntax).
   Two assertions that look different but work around the same solver limitation
   should be in the same category.

2. **Name each category precisely** (e.g., "sequence slice equality not propagated",
   not "sequence issues").

3. **For each category:**
   - Count of quirks
   - Representative examples (problem_id + assertion)
   - Canonical fix pattern (what assertion pattern works around this)
   - 2-sentence explanation of the solver limitation

4. **Flag any diagnosis that seems wrong** or where the evidence doesn't support
   the claimed mechanism.

5. **Identify patterns across unsolved problems** — are they failing for the same
   reasons as the quirks you categorized?

Output your analysis as JSON with this structure:

```json
{
  "quirk_types": {
    "category_name": {
      "count": N,
      "description": "2-sentence description of the solver limitation",
      "canonical_fix": "assert pattern(...);",
      "examples": [
        {"problem_id": "...", "assertion": "...", "confidence": "..."}
      ],
      "subtypes": [
        {"pattern": "...", "count": N}
      ]
    }
  },
  "suspect_diagnoses": [
    {"problem_id": "...", "reason": "why this diagnosis seems wrong"}
  ],
  "unsolved_analysis": "Overall pattern analysis for unsolved problems",
  "summary": {
    "total_quirks": N,
    "categories": N,
    "most_common": "category_name",
    "novel_findings": "anything unexpected"
  }
}
```
