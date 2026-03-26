# Dafny → Verus Translation Pipeline

Automated translation of verified Dafny programs to Verus (Rust verification tool).

## Results

| Metric | Count |
|--------|-------|
| Dafny programs translated | 42 / 95 |
| Genuinely verified in Verus | 42 / 42 |
| Unsound (contain assume(false)) | 0 / 42 |

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

## File Structure

```
programs/
  <problem_id>/
    source.dfy          # Original Dafny task.dfy
    translated.rs       # Step 1 output (compiles, may have assume(false))
    full_translation.rs # Subagent output (full proofs)
    verified.rs         # Final verified version
    attempt_*.rs        # Translation attempts
    proof_attempt_*.rs  # Proof addition attempts
translate.py            # Step 1: skeleton translation via claude -p
translate_subagent.py   # Subagent-based translation (recommended)
add_proofs.py           # Old proof addition via claude -p
verify_all.py           # Batch verification
status.json             # Translation tracking
proof_status.json       # Proof addition tracking
verification_results.json  # Verification results
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
