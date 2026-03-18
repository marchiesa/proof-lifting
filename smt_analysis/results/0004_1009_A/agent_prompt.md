# Problem: 0004_1009_A

## Task file (/Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0004_1009_A/task.dfy)

```dafny
ghost function Max(x: int, y: int): int {
  if x >= y then x else y
}

// The maximum number of games purchasable from costs c using bills a
// (in order). At each game, we may buy it (if the current bill covers
// the cost, consuming that bill) or skip it. This explores ALL valid
// purchasing strategies and returns the maximum count.
ghost function MaxPurchases(c: seq<int>, a: seq<int>): int
  decreases |c|
{
  if |c| == 0 || |a| == 0 then 0
  else if a[0] >= c[0] then
    Max(1 + MaxPurchases(c[1..], a[1..]), MaxPurchases(c[1..], a))
  else
    MaxPurchases(c[1..], a)
}

method GameShopping(c: seq<int>, a: seq<int>) returns (count: int)
  ensures count == MaxPurchases(c, a)
  ensures 0 <= count <= |c|
  ensures count <= |a|
{
  count := 0;
  var i := 0;
  var j := 0;
  while i < |c| && j < |a|
  {
    if a[j] >= c[i] {
      count := count + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}
```

## Verified file (already exists — skip Phase 1)

```dafny
ghost function Max(x: int, y: int): int {
  if x >= y then x else y
}

// The maximum number of games purchasable from costs c using bills a
// (in order). At each game, we may buy it (if the current bill covers
// the cost, consuming that bill) or skip it. This explores ALL valid
// purchasing strategies and returns the maximum count.
ghost function MaxPurchases(c: seq<int>, a: seq<int>): int
  decreases |c|
{
  if |c| == 0 || |a| == 0 then 0
  else if a[0] >= c[0] then
    Max(1 + MaxPurchases(c[1..], a[1..]), MaxPurchases(c[1..], a))
  else
    MaxPurchases(c[1..], a)
}

// MaxPurchases is bounded by both sequence lengths and is non-negative
lemma MaxPurchasesBound(c: seq<int>, a: seq<int>)
  ensures 0 <= MaxPurchases(c, a) <= |c|
  ensures MaxPurchases(c, a) <= |a|
  decreases |c|
{
  if |c| == 0 || |a| == 0 {
  } else if a[0] >= c[0] {
    MaxPurchasesBound(c[1..], a[1..]);
    MaxPurchasesBound(c[1..], a);
  } else {
    MaxPurchasesBound(c[1..], a);
  }
}

// More games available never decreases the maximum purchases
lemma MoreGamesNoWorse(c: seq<int>, a: seq<int>)
  requires |c| > 0
  ensures MaxPurchases(c, a) >= MaxPurchases(c[1..], a)
{
  if |a| == 0 {
  } else if a[0] >= c[0] {
    assert MaxPurchases(c, a) == Max(1 + MaxPurchases(c[1..], a[1..]), MaxPurchases(c[1..], a));
  } else {
  }
}

// One extra bill adds at most 1 to the number of purchases
lemma ExtraBillBounded(c: seq<int>, a: seq<int>)
  requires |a| > 0
  ensures MaxPurchases(c, a) <= MaxPurchases(c, a[1..]) + 1
  decreases |c|
{
  if |c| == 0 {
  } else {
    ExtraBillBounded(c[1..], a);
    MoreGamesNoWorse(c, a[1..]);
  }
}

// Greedy buying is optimal: when we can buy, it's always best to buy
lemma GreedyBuyOptimal(c: seq<int>, a: seq<int>)
  requires |c| > 0 && |a| > 0 && a[0] >= c[0]
  ensures MaxPurchases(c, a) == 1 + MaxPurchases(c[1..], a[1..])
{
  ExtraBillBounded(c[1..], a);
}

method GameShopping(c: seq<int>, a: seq<int>) returns (count: int)
  ensures count == MaxPurchases(c, a)
  ensures 0 <= count <= |c|
  ensures count <= |a|
{
  count := 0;
  var i := 0;
  var j := 0;

  while i < |c| && j < |a|
    invariant 0 <= i <= |c|
    invariant 0 <= j <= |a|
    invariant count >= 0
    invariant count + MaxPurchases(c[i..], a[j..]) == MaxPurchases(c, a)
  {
    if a[j] >= c[i] {
      GreedyBuyOptimal(c[i..], a[j..]);
      assert c[i..][1..] == c[(i+1)..];
      assert a[j..][1..] == a[(j+1)..];
      count := count + 1;
      j := j + 1;
    } else {
      assert c[i..][1..] == c[(i+1)..];
    }
    i := i + 1;
  }
  MaxPurchasesBound(c, a);
}

```

VERIFY_PHASE = false
This problem is already verified. Skip Phase 1 (VERIFY) and go directly to Phase 2 (ANNOTATE).
Start by running full logging on the verified file to produce artifacts.

## Output directory: /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A

IMPORTANT PATHS:
- PROJ_ROOT = /Users/mchiesa/work/projects/2026-02-dafny-liftings
- PROBLEM_DIR = /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A
- Original task: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0004_1009_A/task.dfy

# SMT Quirk Analysis — Per-Problem Agent

You are analyzing a Dafny verification problem to discover SMT solver quirks.

## Your Task

You will be given a Dafny file (`task.dfy`) that has ghost specs and a method body.
VERIFIED_DFY may already exist (from a prior verification pass). Your job depends on
the mode:

**Full mode (VERIFY_PHASE = false):**
1. **VERIFY** — Add loop invariants, assertions, ghost variables, and/or lemma calls
2. **ANNOTATE** — Use the mapping chain to translate SMT-level names to Dafny-level names
3. **ABLATE** — Remove each assertion/invariant you added, one at a time, to find essential ones
4. **DIAGNOSE** — For each essential assertion, investigate WHY the solver needs it
5. **AXIOM** — Propose and test Boogie axioms that would eliminate each essential assertion
6. **REPORT** — Write a structured JSON report with all findings

**Analyze-only mode (VERIFY_PHASE = false):**
Skip step 1. Use the existing `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/verified.dfy` and run steps 2–6.

## Environment

- **Project root:** `/Users/mchiesa/work/projects/2026-02-dafny-liftings` (will be replaced by the orchestrator)
- **Problem dir:** `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A` (will be replaced by the orchestrator)
- **Task file:** `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/task.dfy`
- **Verified file:** `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/verified.dfy` (exists if already verified)
- **Output dir:** `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A` (write all results here)

### Available tools

1. **Dafny verify with full logging:**
   ```bash
   bash /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/helpers/run_dafny_verify.sh <dfy_file> <output_dir> [timeout]
   ```
   Produces: `ast_mapping.json`, `output.bpl`, `output.smt2`, `name_map.json`, `dafny_output.txt`

2. **Quick ablation verify:**
   ```bash
   bash /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/helpers/run_ablation.sh <dfy_file> [timeout]
   ```
   Outputs JSON: `{result, exit_code, errors, time_seconds}`

3. **Axiom test (patch BPL + run Boogie):**
   ```bash
   bash /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/helpers/test_axiom.sh <bpl_file> <axiom_file> [timeout]
   ```
   Patches a BPL file with a proposed axiom and runs Boogie. Returns JSON with pass/fail.

4. **Artifact annotation (BPL + SMT + AST mapping → Dafny-level summary):**
   ```bash
   python3 /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/annotate.py \
       --bpl <output.bpl> \
       --name-map <name_map.json> \
       --ast-mapping <ast_mapping.json> \
       --smt <output.smt2> \
       --dafny-output <dafny_output.txt> \
       -o <annotated_log.json>
   ```
   Produces: axiom catalog with trigger patterns, per-VC assertion tables,
   symbol table mapping $generated@@N to Dafny names.

5. **Standard tools:** Read, Write, Edit, Bash, Glob, Grep for file inspection.

## Phase 1: VERIFY

**Skip this phase if VERIFY_PHASE = false.** Instead, copy `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/verified.dfy`
to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/artifacts/verified.dfy` and run full logging on it:
```bash
mkdir -p /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/artifacts
cp /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/verified.dfy /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/artifacts/verified.dfy
bash /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/helpers/run_dafny_verify.sh \
    /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/artifacts/verified.dfy /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/artifacts/ 60
```

**If VERIFY_PHASE = false:**

1. Read `task.dfy`. Understand the spec (ghost functions/predicates) and the method body.
2. Identify all loops that need invariants.
3. Add loop invariants. Common patterns:
   - Accumulator invariants: `invariant acc == F(s[..i])`
   - Bounds: `invariant 0 <= i <= |s|`
   - Sequence slice equalities: `assert s[..i+1] == s[..i] + [s[i]];` (often needed!)
   - Type preservation: `invariant AllNonNeg(partial)` if required by spec
4. Run verification:
   ```bash
   mkdir -p /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/artifacts
   cp task_with_invariants.dfy /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/artifacts/verified.dfy
   bash /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/helpers/run_dafny_verify.sh \
       /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/artifacts/verified.dfy /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/artifacts/ 60
   ```
5. If verification fails, read the error output, modify the code, and retry.
6. Save each attempt:
   ```
   /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/attempts/01_verified.dfy
   /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/attempts/01_dafny_output.txt
   /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/attempts/02_verified.dfy
   ...
   ```
7. Continue until verification passes or you've tried 5+ approaches.

**Important:** Even if you can't solve it, save your best attempt and all error logs.
Failed attempts are valuable for analysis.

## Phase 2: ANNOTATE

Only if Phase 1 produced artifacts (ast_mapping.json, name_map.json, output.smt2):

```bash
python3 /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/annotate.py \
    --bpl /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/artifacts/output.bpl \
    --name-map /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/artifacts/name_map.json \
    --ast-mapping /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/artifacts/ast_mapping.json \
    --smt /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/artifacts/output.smt2 \
    --dafny-output /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/artifacts/dafny_output.txt \
    -o /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/artifacts/annotated_log.json
```

Read the annotated log. Key sections to examine:
- **axiom_catalog**: Which Dafny functions have axioms and what their trigger patterns are.
  Triggers control when Z3 instantiates quantifiers — missing triggers are a common quirk.
- **assertion_id_table**: Maps Boogie assertion IDs to their BPL text and Dafny source.
  Most IDs are bounds checks/termination; only a few map to user-written spec.
- **vcs**: Per-VC breakdown showing which assertions are checked and which program
  variables are in scope.
- **dafny_errors**: Parsed error messages with line numbers.

## Phase 3: ABLATE

Only if verification passed:

1. Compare your `verified.dfy` with the original `task.dfy`. List every element you added:
   - Loop invariants
   - Assertions
   - Ghost variables
   - Lemma calls
   - Helper functions/lemmas

2. For each added element, create a variant with JUST that element removed.
   Save as `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/evidence/without_<N>.dfy`.

3. Run ablation on each variant:
   ```bash
   bash /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/helpers/run_ablation.sh \
       /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/evidence/without_<N>.dfy 60
   ```

4. Record which removals cause failure and how they fail (timeout vs error, which VC).

5. Write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/ablation_results.json`:
   ```json
   {
     "total_added_elements": 8,
     "essential_elements": [...],
     "non_essential_elements": [...],
     "minimal_set_size": 3
   }
   ```

## Phase 4: DIAGNOSE

For each essential assertion from Phase 3:

1. **Create evidence directory:** `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/evidence/assertion_<N>/`

2. **Save variants:**
   - `with_assertion.dfy` — the full verified file
   - `without_assertion.dfy` — without this specific assertion

3. **Ghost variable probe:** Create a variant that introduces the assertion's
   sub-expressions as ghost variables but does NOT assert their equality.
   For example, if the assertion is `assert a[..i+1] == a[..i] + [a[i]];`,
   create:
   ```dafny
   ghost var lhs := a[..i+1];
   ghost var rhs := a[..i] + [a[i]];
   // NO assert lhs == rhs;
   ```
   Run ablation on this. If it still fails → the solver needs the explicit equality,
   not just the terms.

4. **Run full logging on the without-assertion variant:**
   ```bash
   bash /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/helpers/run_dafny_verify.sh \
       /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/evidence/assertion_<N>/without_assertion.dfy \
       /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/evidence/assertion_<N>/without_artifacts/ 60
   ```

5. **Extract and analyze the SMT log.** This is the most important step.

   Read the SMT file (`without_artifacts/output.smt2`) and look for:

   a. **Relevant axioms and their triggers.** Find all `(assert (! (forall ...` that
      mention the Dafny functions used in the assertion. Extract the `:pattern` clauses.
      These are the triggers Z3 uses for e-matching. Ask: does the failing VC contain
      terms that match these triggers? If not, that's the gap.

   b. **The failing VC body.** Find the VC section (between `(push 1)` and `(pop 1)`)
      for the failing verification condition. Look at what terms Z3 has available.
      Translate $generated@@N names to Dafny names using the name_map.

   c. **Sequence operations.** If the assertion involves sequences, look for these
      specific Boogie/SMT patterns:
      - `Seq#Take(Seq#Take(s, m), n)` — nested Takes with no simplification axiom
      - `Seq#Take(Seq#Append(s, t), n)` — Take of Append, only fires when `n == |s|`
      - `Seq#Take(s, Seq#Length(s))` — Take of full length, no simplification
      - `Seq#Append(s, Seq#Empty())` — Append empty, needs literal `Seq#Empty()`

   d. **Compare with and without.** Look at the SMT from the WITH-assertion artifacts
      (`/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/artifacts/output.smt2`). The assertion adds explicit equalities
      to the VC. What terms get merged in the e-graph when the equality is asserted?

   e. **Write the analysis** to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/evidence/assertion_<N>/smt_analysis.md`:
      ```markdown
      ## Assertion: assert s[..i+1] == s[..i] + [s[i]];

      ### Dafny → SMT translation
      - LHS: s[..i+1] → Seq#Take(s, i+1)
      - RHS: s[..i] + [s[i]] → Seq#Append(Seq#Take(s, i), Seq#Build(Seq#Index(s, i)))

      ### Relevant axioms and triggers
      [List the axioms from the preamble that involve Seq#Take, Seq#Append, etc.]
      [Show their trigger patterns]

      ### What the failing VC contains
      [List key terms in the VC body, translated to Dafny]

      ### The gap
      [Explain precisely what Z3 cannot derive and why]
      ```

6. **Write diagnosis:** Based on all evidence, what specific SMT limitation does
   this assertion work around? Be precise:
   - "Sequence slice equality not propagated by e-matching"
   - "Trigger pattern for quantifier Q doesn't match term T"
   - "Recursive function not unfolded beyond depth N"
   - "Nonlinear arithmetic: solver can't prove a*b == b*a"
   - "Missing axiom: Seq#Take(Seq#Take(s,m),n) has no simplification"
   - If unsure, say what evidence you have and what you'd need to be sure.

7. **Write reproduce.sh:**
   ```bash
   #!/bin/bash
   echo "=== With assertion (should pass) ==="
   dafny verify with_assertion.dfy --verification-time-limit 60
   echo "=== Without assertion (should fail) ==="
   dafny verify without_assertion.dfy --verification-time-limit 60
   echo "=== Ghost vars only ==="
   dafny verify ghost_var_variant.dfy --verification-time-limit 60
   ```

## Phase 5: AXIOM

For each essential assertion from Phase 3, propose a Boogie axiom that would make it
unnecessary, and TEST it.

### Background: Boogie axiom structure

Boogie axioms are universally quantified formulas with trigger patterns. Example:
```boogie
axiom (forall s: Seq, m: int, n: int ::
  { Seq#Take(Seq#Take(s, m), n) }
  0 <= n && n <= m && m <= Seq#Length(s)
     ==> Seq#Take(Seq#Take(s, m), n) == Seq#Take(s, n));
```

The `{ ... }` is the trigger pattern — Z3 only instantiates the axiom when a matching
term appears in the e-graph.

### Known missing axioms (from our prior analysis)

These are axioms we've already identified as missing from Dafny's Boogie prelude:

1. **Take-of-Take simplification:**
   ```boogie
   axiom (forall s: Seq, m: int, n: int ::
     { Seq#Take(Seq#Take(s, m), n) }
     0 <= n && n <= m && m <= Seq#Length(s)
        ==> Seq#Take(Seq#Take(s, m), n) == Seq#Take(s, n));
   ```

2. **Generalized Take-of-Append** (n ≤ |s|):
   ```boogie
   axiom (forall s: Seq, t: Seq, n: int ::
     { Seq#Take(Seq#Append(s, t), n) }
     0 <= n && n <= Seq#Length(s)
        ==> Seq#Take(Seq#Append(s, t), n) == Seq#Take(s, n));
   ```

3. **Take-of-full-length:**
   ```boogie
   axiom (forall s: Seq ::
     { Seq#Length(s) }
     Seq#Take(s, Seq#Length(s)) == s);
   ```

### Steps

For each essential assertion:

1. **Analyze the SMT gap** (from Phase 4) and determine what axiom would close it.
   If it matches a known missing axiom above, use that. Otherwise, propose a new one.

2. **Write the proposed axiom** to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/evidence/assertion_<N>/proposed_axiom.bpl`:
   ```boogie
   // Proposed axiom for: assert s[..i+1] == s[..i] + [s[i]];
   // Gap: Seq#Take(Seq#Take(s, i+1), i) has no simplification
   axiom (forall s: Seq, m: int, n: int ::
     { Seq#Take(Seq#Take(s, m), n) }
     0 <= n && n <= m && m <= Seq#Length(s)
        ==> Seq#Take(Seq#Take(s, m), n) == Seq#Take(s, n));
   ```

3. **Test the axiom.** Use the BPL from the without-assertion variant:
   ```bash
   bash /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/helpers/test_axiom.sh \
       /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/evidence/assertion_<N>/without_artifacts/output.bpl \
       /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/evidence/assertion_<N>/proposed_axiom.bpl \
       60
   ```
   This patches the BPL with the axiom and runs Boogie. If Boogie verifies,
   the axiom eliminates the need for the assertion.

4. **Record the result** in the evidence directory:
   - `axiom_test_result.json`: `{axiom, test_passed, boogie_output}`
   - If the test fails, analyze why. Maybe the axiom needs different triggers,
     or the gap requires multiple axioms.

5. **Collect all proposed axioms** into `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/proposed_axioms.bpl`.
   This file should contain ALL axioms proposed for this problem, with comments
   explaining which assertion each one replaces and whether the test passed.

## Phase 6: REPORT

Write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/report.json` with:

```json
{
  "problem_id": "NNNN_problem_name",
  "solved": true,
  "attempts": 3,
  "verification_time_seconds": 12.5,
  "elements_added": {
    "invariants": ["invariant 0 <= i <= |s|", "invariant acc == Sum(s[..i])"],
    "assertions": ["assert s[..i+1] == s[..i] + [s[i]];"],
    "ghost_vars": [],
    "lemma_calls": [],
    "helper_functions": []
  },
  "essential_elements": [
    {
      "element": "assert s[..i+1] == s[..i] + [s[i]];",
      "line": 42,
      "type": "assertion",
      "essential": true,
      "without_it": {
        "result": "timeout",
        "failing_vc": "invariant_maintained",
        "dafny_error": "this invariant could not be proved to be maintained"
      },
      "diagnosis": {
        "mechanism": "missing Take-of-Take axiom",
        "ghost_var_test": "failed",
        "confidence": "high",
        "explanation": "Recursive function unfolds on Seq#Take(s,i+1) producing Seq#Take(Seq#Take(s,i+1),i) which has no simplification axiom. The assertion forces equality via extensionality, merging e-classes.",
        "smt_gap": "Seq#Take(Seq#Take(s,m),n) has no axiom to simplify to Seq#Take(s,n)"
      },
      "proposed_axiom": {
        "boogie": "axiom (forall s: Seq, m: int, n: int :: { Seq#Take(Seq#Take(s, m), n) } 0 <= n && n <= m && m <= Seq#Length(s) ==> Seq#Take(Seq#Take(s, m), n) == Seq#Take(s, n));",
        "test_passed": true,
        "axiom_category": "take_of_take"
      }
    }
  ],
  "non_essential_elements": [
    {
      "element": "ghost var prefix := s[..i];",
      "type": "ghost_var",
      "essential": false
    }
  ],
  "proposed_axioms_file": "/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0004_1009_A/proposed_axioms.bpl",
  "verification_commands": {
    "verify": "dafny verify verified.dfy --verification-time-limit 60",
    "ablation_example": "dafny verify evidence/without_1.dfy --verification-time-limit 60"
  },
  "notes": "Free-form observations about this problem."
}
```

## Guidelines

- **Be thorough but efficient.** Don't spend more than 5 minutes on any single sub-task.
- **Save everything.** Failed attempts, error logs, intermediate files — all are useful.
- **Be precise in diagnoses.** "The solver can't do X" is better than "something is wrong."
- **Don't guess mechanisms.** If the evidence is inconclusive, say so.
- **Use the annotation pipeline.** It's the key differentiator — SMT logs with Dafny names.
- **Read the actual SMT log.** Don't just rely on the annotation output. Look at the raw
  SMT-LIB to understand what terms Z3 has and what axioms are available.
- **Write reproducible evidence.** Every diagnosis should come with a `dafny verify` command
  that demonstrates the issue.
- **Test every proposed axiom.** Don't just theorize — use test_axiom.sh to verify it works.

