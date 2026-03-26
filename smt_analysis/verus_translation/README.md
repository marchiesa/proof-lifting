# Dafny → Verus Translation Pipeline

Automated translation of verified Dafny programs to Verus (Rust verification tool).

## Results

| Metric | Count |
|--------|-------|
| Dafny programs translated | 42 / 95 |
| Genuinely verified in Verus | 37 / 42 |
| Unsound (contain assume(false)) | 5 / 42 |

The 5 unsound programs were produced by the early `claude -p` approach (see below).
All 35 programs produced by the subagent approach are fully verified with no `assume(false)`.

## Verification Command

```bash
/tmp/verus_install/verus-arm64-macos/verus <file.rs>
```

Install Verus from [releases](https://github.com/verus-lang/verus/releases):
```bash
curl -sL <arm64-macos-zip-url> -o verus.zip
unzip verus.zip -d verus_install
cd verus_install/verus-arm64-macos
bash macos_allow_gatekeeper.sh
rustup install 1.94.0-aarch64-apple-darwin
./verus --version
```

## Pipeline

### Step 1: Translation (translate.py)

Translates `task.dfy` (spec + method signature) to Verus using `claude -p`.
Produces `translated.rs` that compiles with `verus --no-verify`.

```bash
python3 translate.py --limit 10
```

This step only ensures the code type-checks. Proof bodies are left as
`proof { assume(false); }` placeholders. Success rate: ~66%.

### Step 2: Proof Addition — Subagent Approach (recommended)

Uses Claude Code Agent subagents with full tool access (read files, run verus,
iterate on errors). Each subagent:

1. Reads the Dafny `verified.dfy` (which has working proofs)
2. Reads the Verus `translated.rs` (skeleton)
3. Translates the full proof strategy from Dafny to Verus
4. Runs `verus` to check
5. Iterates up to 10 times on errors

**This approach achieved 100% success rate (35/35)** on all programs attempted.

The key was providing the **verified Dafny file** (with working proofs) as reference,
not just the spec. The subagent uses the Dafny proof strategy as a guide for what
invariants, assertions, and lemmas are needed in Verus.

Example subagent prompt:
```
Translate this verified Dafny program to Verus. Read <verified.dfy>.
Translate EVERYTHING including proof bodies. No assume(false).
Write to <output.rs>. Run verus. Iterate until verified or 10 attempts.
```

### Step 2 (old): Proof Addition — claude -p approach (not recommended)

Uses `claude -p` (print mode, no tools) to add proofs. One-shot prompt → response.
Success rate: ~30%. Produced the 5 unsound files with `assume(false)`.

```bash
python3 add_proofs.py --workers 10 --max-attempts 10
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

## File Structure

```
programs/
  <problem_id>/
    source.dfy          # Original Dafny task.dfy
    translated.rs       # Step 1 output (compiles, may have assume(false))
    full_translation.rs # Step 2 output (full proofs)
    verified.rs         # Final verified version (copy of full_translation.rs)
    attempt_*.rs        # Translation attempts
    proof_attempt_*.rs  # Proof addition attempts
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

# Check for assume(false)
grep -rl "assume(false)" programs/*/verified.rs
```
