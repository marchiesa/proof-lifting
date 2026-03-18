Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Angry Students
It's a walking tour day in SIS.Winter, so $$$t$$$ groups of students are visiting Torzhok. Streets of Torzhok are so narrow that students have to go in a row one after another.

Initially, some students are angry. Let's describe a group of students by a string of capital letters "A" and "P":

- "A" corresponds to an angry student
- "P" corresponds to a patient student

Such string describes the row from the last to the first student.

Every minute every angry student throws a snowball at the next student. Formally, if an angry student corresponds to the character with index $$$i$$$ in the string describing a group then they will throw a snowball at the student that corresponds to the character with index $$$i+1$$$ (students are given from the last to the first student). If the target student was not angry yet, they become angry. Even if the first (the rightmost in the string) student is angry, they don't throw a snowball since there is no one in front of them.

Let's look at the first example test. The row initially looks like this: PPAP. Then, after a minute the only single angry student will throw a snowball at the student in front of them, and they also become angry: PPAA. After that, no more students will become angry.

Your task is to help SIS.Winter teachers to determine the last moment a student becomes angry for every group.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0084_1287_A/task.dfy

```dafny
ghost predicate ValidState(s: seq<char>)
{
  forall i | 0 <= i < |s| :: s[i] == 'A' || s[i] == 'P'
}

// One simultaneous round: every angry student makes the next student angry
ghost function OneStep(s: seq<char>): seq<char>
{
  seq(|s|, j requires 0 <= j < |s| =>
    if s[j] == 'A' || (j > 0 && s[j-1] == 'A' && s[j] == 'P') then 'A' else s[j])
}

// Apply the snowball-throwing rule `steps` times
ghost function Simulate(s: seq<char>, steps: nat): seq<char>
  decreases steps
{
  if steps == 0 then s else Simulate(OneStep(s), steps - 1)
}

// No student becomes angry in the next round
ghost predicate IsFixedPoint(s: seq<char>)
{
  OneStep(s) == s
}

method {:verify false} AngryStudents(s: string) returns (steps: int)
  decreases *
  requires ValidState(s)
  ensures steps >= 0
  ensures IsFixedPoint(Simulate(s, steps))
  ensures forall k: int | 0 <= k < steps :: !IsFixedPoint(Simulate(s, k))
{
  var n := |s|;
  var line := new char[n];
  var i := 0;
  while i < n {
    line[i] := s[i];
    i := i + 1;
  }

  steps := 0;
  while true
    decreases *
  {
    var flag := false;
    var j := n - 1;
    while j >= 0 {
      if line[j] == 'A' && j + 1 < n && line[j + 1] == 'P' {
        line[j + 1] := 'A';
        flag := true;
      }
      j := j - 1;
    }
    if !flag {
      break;
    }
    steps := steps + 1;
  }
}

method {:verify false} Main()
  decreases *
{
  var r: int;

  // Test 1
  r := AngryStudents("PPAP");
  expect r == 1, "PPAP";

  // Test 2
  r := AngryStudents("APPAPPPAPPPP");
  expect r == 4, "APPAPPPAPPPP";
  r := AngryStudents("AAP");
  expect r == 1, "AAP";
  r := AngryStudents("PPA");
  expect r == 0, "PPA";

  // Test 3
  r := AngryStudents("A");
  expect r == 0, "A";
  r := AngryStudents("P");
  expect r == 0, "P";
  r := AngryStudents("AP");
  expect r == 1, "AP";
  r := AngryStudents("PA");
  expect r == 0, "PA";
  r := AngryStudents("PPPPAPPP");
  expect r == 3, "PPPPAPPP";
  r := AngryStudents("PPPPPPPA");
  expect r == 0, "PPPPPPPA";
  r := AngryStudents("APPPPPPP");
  expect r == 7, "APPPPPPP";
  r := AngryStudents("PPPPPPAP");
  expect r == 1, "PPPPPPAP";
  r := AngryStudents("PPPPPAPP");
  expect r == 2, "PPPPPAPP";
  r := AngryStudents("PPPAPPPP");
  expect r == 4, "PPPAPPPP";

  // Test 4
  r := AngryStudents("PPPP");
  expect r == 0, "PPPP";
  r := AngryStudents("APPP");
  expect r == 3, "APPP";
  r := AngryStudents("PAPP");
  expect r == 2, "PAPP";
  r := AngryStudents("AAPP");
  expect r == 2, "AAPP";
  r := AngryStudents("PPAP");
  expect r == 1, "PPAP 2";
  r := AngryStudents("APAP");
  expect r == 1, "APAP";
  r := AngryStudents("PAAP");
  expect r == 1, "PAAP";
  r := AngryStudents("AAAP");
  expect r == 1, "AAAP";
  r := AngryStudents("PPPA");
  expect r == 0, "PPPA";
  r := AngryStudents("APPA");
  expect r == 2, "APPA";
  r := AngryStudents("PAPA");
  expect r == 1, "PAPA";
  r := AngryStudents("AAPA");
  expect r == 1, "AAPA";
  r := AngryStudents("PPAA");
  expect r == 0, "PPAA";
  r := AngryStudents("APAA");
  expect r == 1, "APAA";
  r := AngryStudents("PAAA");
  expect r == 0, "PAAA";
  r := AngryStudents("AAAA");
  expect r == 0, "AAAA";

  // Test 5
  r := AngryStudents("PAPPPAPAAPAAPAAPPAAAPPAPPAPAAAAPPAPPAPPPAAAAAAPPAAAPAAAAAPAPAPAAAAPPAPAAAAPPAPPPPPAAAAAAAPAAAAPAPPAP");
  expect r == 5, "long string";

  print "All tests passed\n";
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0084_1287_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0084_1287_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0084_1287_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0084_1287_A/ (create the directory if needed).
