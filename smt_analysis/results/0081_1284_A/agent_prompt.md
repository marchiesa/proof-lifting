Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: New Year and Naming
Happy new year! The year 2020 is also known as Year Gyeongja (경자년, gyeongja-nyeon) in Korea. Where did the name come from? Let's briefly look at the Gapja system, which is traditionally used in Korea to name the years.

There are two sequences of $$$n$$$ strings $$$s_1, s_2, s_3, \ldots, s_{n}$$$ and $$$m$$$ strings $$$t_1, t_2, t_3, \ldots, t_{m}$$$. These strings contain only lowercase letters. There might be duplicates among these strings.

Let's call a concatenation of strings $$$x$$$ and $$$y$$$ as the string that is obtained by writing down strings $$$x$$$ and $$$y$$$ one right after another without changing the order. For example, the concatenation of the strings "code" and "forces" is the string "codeforces".

The year 1 has a name which is the concatenation of the two strings $$$s_1$$$ and $$$t_1$$$. When the year increases by one, we concatenate the next two strings in order from each of the respective sequences. If the string that is currently being used is at the end of its sequence, we go back to the first string in that sequence.

For example, if $$$n = 3, m = 4, s = $$${"a", "b", "c"}, $$$t =$$$ {"d", "e", "f", "g"}, the following table denotes the resulting year names. Note that the names of the years may repeat.

You are given two sequences of strings of size $$$n$$$ and $$$m$$$ and also $$$q$$$ queries. For each query, you will be given the current year. Could you find the name corresponding to the given year, according to the Gapja system?

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0081_1284_A/task.dfy

```dafny
// The position in a cyclic sequence of given period for a given year.
// Year 1 starts at position 0; each subsequent year advances by 1, wrapping around.
ghost function CyclicIndex(year: int, period: int): int
  requires year >= 1
  requires period > 0
  ensures 0 <= CyclicIndex(year, period) < period
{
  (year - 1) % period
}

// The Gapja name for a year: concatenation of the cyclically selected
// string from each of the two naming sequences.
ghost function GapjaName(year: int, s: seq<string>, t: seq<string>): string
  requires year >= 1
  requires |s| > 0
  requires |t| > 0
{
  s[CyclicIndex(year, |s|)] + t[CyclicIndex(year, |t|)]
}

method NewYearNaming(n: int, m: int, s: seq<string>, t: seq<string>, queries: seq<int>) returns (results: seq<string>)
  requires n > 0 && m > 0
  requires |s| == n && |t| == m
  requires forall i | 0 <= i < |queries| :: queries[i] >= 1
  ensures |results| == |queries|
  ensures forall i | 0 <= i < |queries| :: results[i] == GapjaName(queries[i], s, t)
{
  results := [];
  for i := 0 to |queries| {
    var x := queries[i] - 1;
    results := results + [s[x % n] + t[x % m]];
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0081_1284_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0081_1284_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0081_1284_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0081_1284_A/ (create the directory if needed).
