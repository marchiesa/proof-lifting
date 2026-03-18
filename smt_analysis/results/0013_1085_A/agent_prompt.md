Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Right-Left Cipher
Polycarp loves ciphers. He has invented his own cipher called Right-Left.

Right-Left cipher is used for strings. To encrypt the string $$$s=s_{1}s_{2} \dots s_{n}$$$ Polycarp uses the following algorithm:

- he writes down $$$s_1$$$,
- he appends the current word with $$$s_2$$$ (i.e. writes down $$$s_2$$$ to the right of the current result),
- he prepends the current word with $$$s_3$$$ (i.e. writes down $$$s_3$$$ to the left of the current result),
- he appends the current word with $$$s_4$$$ (i.e. writes down $$$s_4$$$ to the right of the current result),
- he prepends the current word with $$$s_5$$$ (i.e. writes down $$$s_5$$$ to the left of the current result),
- and so on for each position until the end of $$$s$$$.

For example, if $$$s$$$="techno" the process is: "t" $$$\to$$$ "te" $$$\to$$$ "cte" $$$\to$$$ "cteh" $$$\to$$$ "ncteh" $$$\to$$$ "ncteho". So the encrypted $$$s$$$="techno" is "ncteho".

Given string $$$t$$$ — the result of encryption of some string $$$s$$$. Your task is to decrypt it, i.e. find the string $$$s$$$.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0013_1085_A/task.dfy

```dafny
// The Right-Left encryption: builds a string by writing s[0], then alternately
// appending (odd indices) and prepending (even indices >= 2) each subsequent character.
ghost function Encrypt(s: string): string
  decreases |s|
{
  if |s| == 0 then ""
  else if |s| == 1 then [s[0]]
  else if |s| % 2 == 0 then
    // Last character index is odd → append to the right
    Encrypt(s[..|s|-1]) + [s[|s|-1]]
  else
    // Last character index is even (>=2) → prepend to the left
    [s[|s|-1]] + Encrypt(s[..|s|-1])
}

// s is a valid decryption of ciphertext t iff encrypting s produces t
ghost predicate IsDecryptionOf(s: string, t: string)
{
  |s| == |t| && Encrypt(s) == t
}

method Decrypt(t: string) returns (s: string)
  ensures IsDecryptionOf(s, t)
{
  var n := |t|;
  if n == 0 {
    s := "";
    return;
  }
  var mid := (n - 1) / 2;
  s := [t[mid]];
  var u1: int := mid + 1;
  var u2: int := mid - 1;
  while u1 < n && u2 >= 0
  {
    s := s + [t[u1]];
    s := s + [t[u2]];
    u1 := u1 + 1;
    u2 := u2 - 1;
  }
  if n % 2 == 0 {
    s := s + [t[n - 1]];
  }
}
```

## Instructions:

1. Read the code carefully. Understand what the method does and what the spec requires.

2. Add loop invariants for every loop. Common patterns:
   - Bounds: `invariant 0 <= i <= |s|`
   - Accumulator: `invariant acc == F(s[..i])` for recursive ghost functions
   - Sequence slicing: `assert s[..i+1] == s[..i] + [s[i]];` before using F(s[..i+1])
   - Full slice identity: `assert s[..|s|] == s;` after loops that process entire sequences
   - Type preservation: `invariant AllNonNeg(s[..i])` if needed by the spec

3. Add helper lemmas if needed (e.g., SumAppend, induction lemmas).

4. Run dafny verify:
   ```bash
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0013_1085_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0013_1085_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0013_1085_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0013_1085_A/ (create the directory if needed).
