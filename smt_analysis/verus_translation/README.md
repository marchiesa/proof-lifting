# Dafny → Verus Translation + Quirk Classification Pipeline

Automated translation of verified Dafny programs to Verus (Rust verification tool),
followed by brittleness detection and SMT quirk classification.

## Results

### Translation

| Metric | Count |
|--------|-------|
| Dafny programs translated | 95 / 95 |
| Verified in Verus | 94 / 95 (1 broken by Verus version change) |
| Unsound (contain assume(false)) | 0 |

### Brittleness (10 Z3 random seeds)

| Metric | Count |
|--------|-------|
| Stable (pass all 10 seeds) | 93 |
| Brittle (pass some seeds) | 1 (`0017_1005_A`, fixed in `verified_not_brittle.rs`) |
| Always fails | 1 (`0103_1305_A`, renamed to `unverified.rs`) |

### Quirk Classification (93 stable programs)

| Category | Assertions | Programs | % |
|----------|-----------|----------|---|
| A. Missing axioms (seq extensionality) | 44 | 20 | 25.4% |
| B. E-matching gaps | 55 | 30 | 31.8% |
| C. Nonlinear arithmetic | 40 | 16 | 23.1% |
| D. Propagation | 33 | 7 | 19.1% |
| **Total** | **173** | **57** | |

Programs with no quirk assertions: 36 / 93.
Lemma calls (proof-level reasoning) are excluded from the quirk count.

Detailed sub-categories:

| Sub-category | Count | % |
|---|---|---|
| A2. Take-full (`s.take(n) =~= s`) | 21 | 12.1% |
| A4. Other seq extensionality | 12 | 6.9% |
| A3. Push/append | 9 | 5.2% |
| A1. Subrange-of-subrange | 2 | 1.2% |
| B1. Trigger forall | 30 | 17.3% |
| B2. Trigger existential | 25 | 14.5% |
| C1. Nonlinear arithmetic | 40 | 23.1% |
| D1. Propagation | 33 | 19.1% |

## Verification Command

```bash
# Install Verus
curl -sL <arm64-macos-zip-url> -o verus.zip
unzip verus.zip -d verus_install
cd verus_install/verus-arm64-macos
bash macos_allow_gatekeeper.sh
rustup install 1.94.0-aarch64-apple-darwin

# Verify a program
./verus <file.rs>
```

## Technique: Claude Code Subagents

The translation is done by **Claude Code spawning internal subagents**. Each subagent
is given one Dafny program to translate to Verus. It has full tool access: it can read
files, write files, run `verus`, see errors, and iterate. The key insight is providing
the **verified Dafny file** (which contains working proofs) as reference — the subagent
uses the Dafny proof strategy as a guide for what invariants, assertions, and lemmas
are needed in Verus.

**Success rate: 100% (42/42)** when using this approach with the verified Dafny as reference.

### How it works

1. The user asks Claude Code to translate Dafny programs to Verus
2. Claude Code launches one Agent subagent per problem, in parallel (up to ~5 at a time)
3. Each subagent reads the Dafny `verified.dfy`, translates it to Verus, runs `verus`, and iterates on errors
4. Results are written to `programs/<problem_id>/verified.rs`

### Prompt to give Claude Code (to launch subagents)

To translate all remaining problems, tell Claude Code:

```
Translate the remaining Dafny programs to Verus. For each problem in
smt_analysis/results/*/verified.dfy that doesn't yet have a clean
verified.rs in smt_analysis/verus_translation/programs/, launch a
subagent to translate it. Run 5 in parallel. Use the subagent prompt
documented in the README.
```

### Subagent prompt (used by Claude Code for each problem)

This is the exact prompt that Claude Code passes to each Agent subagent:

```
Translate this verified Dafny program to Verus (Rust verification tool).
Translate EVERYTHING including all proof bodies, lemmas, and assertions.
Do NOT use assume(false) anywhere.

Read the Dafny source at <path to verified.dfy>

Verus translation rules:
- ghost function → spec fn
- ghost predicate → spec fn returning bool
- method → fn
- lemma → proof fn
- Use int/Seq<int> in spec mode, i64/Vec<i64> in exec mode
- a@.map(|_idx, x: i64| x as int) to convert Vec<i64> to Seq<int>
- forall i | cond :: body → forall|i: int| cond ==> body
- exists i | cond :: body → exists|i: int| cond && body
- s[..n] → s.take(n), s[n..] → s.skip(n), |s| → s.len()
- assert a[..i+1] == a[..i] + [a[i]] → assert(s.take(i+1).drop_last() =~= s.take(i))
- assert a[..|a|] == a → assert(s.take(s.len() as int) =~= s)
- Use by(nonlinear_arith) for nonlinear arithmetic
- Use reveal_with_fuel(fn_name, N) for recursive spec function unfolding
- Use #[trigger] annotations on quantified expressions
- Use proof { } blocks for ghost reasoning in exec functions
- Add decreases clauses to all loops
- Wrap in verus! { }, add use vstd::prelude::*; and fn main() {}

Write the complete translated file to <path to full_translation.rs>
Run: /tmp/verus_install/verus-arm64-macos/verus <path to full_translation.rs>
If it fails, read the errors and fix. Iterate until it verifies or you've
tried 10 times. If it verifies, copy the file to verified.rs in the same directory.
```

### Alternative: Automated script (less effective)

For fully automated translation without manual Agent launches, use
`translate_subagent.py --run`. This calls `claude -p` in a loop with
parallel workers. Lower success rate (~70%) because `claude -p` has no
tool access — it can't run verus or read error output interactively.

```bash
python3 translate_subagent.py --run --workers 10 --max-attempts 10
```

## Verus Proof Patterns

Key patterns discovered during translation (not needed in Dafny):

| Pattern | Verus | Dafny equivalent |
|---------|-------|-----------------|
| Nonlinear arithmetic | `by(nonlinear_arith)` or vstd lemmas | Automatic or simple `assert` |
| Recursive function unfolding | `reveal_with_fuel(fn_name, N)` | Automatic |
| Sequence extensionality | `assert(s1 =~= s2)` | `assert s1 == s2` |
| Quantifier triggers | `#[trigger]` annotations required | Automatic inference |
| Division semantics | Explicit Euclidean vs truncation | Euclidean by default |
| Proof code in exec | `proof { ... }` blocks | Inline assertions |
| GCD termination | `#[via_fn]` proof function | Automatic with `decreases` |
| Loop termination | `decreases` always required | Often inferred |
| Trivial NLA facts | `by(nonlinear_arith)` even for `0*x==0` | Automatic |
| Overflow checking | Explicit i64 bounds preconditions | Unbounded int by default |

## Quirk Classification Pipeline

The classification pipeline mirrors the Dafny `classify_quirks.py` but adapted for Verus syntax.

### Step 1: Brittleness detection

```bash
# Check all programs with 10 Z3 random seeds
python3 verus_check_brittleness.py --seeds 10

# Check specific problem
python3 verus_check_brittleness.py --problem 0010_1043_A --seeds 10
```

Output: `verus_brittleness_results.json`

Brittle programs should be fixed (add intermediate assertions until all seeds pass)
and saved as `verified_not_brittle.rs`.

### Step 2: Quirk classification (ablation + categorization)

```bash
# Run on all stable programs (excludes brittle/broken from brittleness results)
python3 verus_classify_quirks.py --all

# Run on specific problem(s)
python3 verus_classify_quirks.py --problem 0010_1043_A

# Just extract and show assertions (no ablation)
python3 verus_classify_quirks.py --extract-only --problem 0010_1043_A
```

Output: `verus_quirk_classification.json`

The pipeline:
1. **Extract** individual `assert(...)` statements from executable function bodies (`fn`).
   Enters `proof { }` blocks and extracts each assertion separately.
   Skips assertions in `proof fn` / `spec fn` (equivalent to Dafny lemma bodies).
2. **Ablate** — remove each assertion one at a time, run `verus`, check if verification fails.
   If it fails → essential. If it still passes → non-essential.
3. **Classify** — pattern-match essential assertions into categories:
   - **A** (missing axioms): `=~=` assertions (sequence extensionality)
   - **B** (e-matching): `assert forall`, existential witnesses, predicate evaluations
   - **C** (NLA): `by(nonlinear_arith)` assertions
   - **D** (propagation): simple equalities and bounds

Lemma calls (`sum_append(a, i)`, `product_bound(...)`, etc.) are detected and
**excluded** — they represent proof-level reasoning, not SMT gaps.

## File Structure

```
programs/
  <problem_id>/
    source.dfy              # Original Dafny task.dfy
    translated.rs           # Step 1 output (compiles, may have assume(false))
    full_translation.rs     # Subagent output (full proofs)
    verified.rs             # Final verified version
    verified_not_brittle.rs # Fixed version for brittle programs
    unverified.rs           # Broken programs (fail with current Verus)
    attempt_*.rs            # Translation attempts
    proof_attempt_*.rs      # Proof addition attempts

# Translation scripts
translate.py              # Step 1: skeleton translation via claude -p
translate_subagent.py     # Subagent-based translation (recommended)
add_proofs.py             # Old proof addition via claude -p
verify_all.py             # Batch verification
status.json               # Translation tracking

# Classification scripts and results
verus_check_brittleness.py      # Seed-variation brittleness detection
verus_brittleness_results.json  # Brittleness results (per-problem, per-seed)
verus_classify_quirks.py        # Ablation + quirk classification pipeline
verus_quirk_classification.json # Classification results (per-problem, per-assertion)
```

## Reproducing

```bash
# Verify all programs
for f in programs/*/verified.rs; do
    echo "=== $(basename $(dirname $f)) ==="
    /tmp/verus_install/verus-arm64-macos/verus "$f" 2>&1 | tail -1
done

# Check for assume(false) — should return nothing
grep -rl "assume(false)" programs/*/verified.rs

# Count verified
ls programs/*/verified.rs | wc -l
```
