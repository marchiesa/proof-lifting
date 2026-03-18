Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Divide it!
You are given an integer $$$n$$$.

You can perform any of the following operations with this number an arbitrary (possibly, zero) number of times:

1. Replace $$$n$$$ with $$$\frac{n}{2}$$$ if $$$n$$$ is divisible by $$$2$$$;
2. Replace $$$n$$$ with $$$\frac{2n}{3}$$$ if $$$n$$$ is divisible by $$$3$$$;
3. Replace $$$n$$$ with $$$\frac{4n}{5}$$$ if $$$n$$$ is divisible by $$$5$$$.

For example, you can replace $$$30$$$ with $$$15$$$ using the first operation, with $$$20$$$ using the second operation or with $$$24$$$ using the third operation.

Your task is to find the minimum number of moves required to obtain $$$1$$$ from $$$n$$$ or say that it is impossible to do it.

You have to answer $$$q$$$ independent queries.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0102_1176_A/task.dfy

```dafny
// Whether n can be reduced to 1 in exactly `steps` moves,
// where each move is one of the three problem-defined operations.
ghost predicate ReachableInSteps(n: int, steps: nat)
  decreases steps
{
  if steps == 0 then
    n == 1
  else
    (n % 2 == 0 && ReachableInSteps(n / 2, steps - 1)) ||
    (n % 3 == 0 && ReachableInSteps(2 * n / 3, steps - 1)) ||
    (n % 5 == 0 && ReachableInSteps(4 * n / 5, steps - 1))
}

// `steps` is the minimum number of moves to reduce n to 1.
ghost predicate IsMinSteps(n: int, steps: nat)
{
  ReachableInSteps(n, steps) &&
  forall k: nat :: k < steps ==> !ReachableInSteps(n, k)
}

// No sequence of operations can reduce n to 1.
ghost predicate Impossible(n: int)
{
  forall k: nat :: !ReachableInSteps(n, k)
}

method DivideIt(n: int) returns (ans: int)
  requires n >= 1
  ensures (ans == -1 && Impossible(n)) ||
          (ans >= 0 && IsMinSteps(n, ans as nat))
{
  ans := 0;
  var m := n;
  while m % 2 == 0 {
    ans := ans + 1;
    m := m / 2;
  }
  while m % 3 == 0 {
    ans := ans + 2;
    m := m / 3;
  }
  while m % 5 == 0 {
    ans := ans + 3;
    m := m / 5;
  }
  if m != 1 {
    ans := -1;
  }
  return;
}

method Main()
{
  // Test 1 cases
  var r1 := DivideIt(1);
  expect r1 == 0, "DivideIt(1) failed";

  var r2 := DivideIt(10);
  expect r2 == 4, "DivideIt(10) failed";

  var r3 := DivideIt(25);
  expect r3 == 6, "DivideIt(25) failed";

  var r4 := DivideIt(30);
  expect r4 == 6, "DivideIt(30) failed";

  var r5 := DivideIt(14);
  expect r5 == -1, "DivideIt(14) failed";

  var r6 := DivideIt(27);
  expect r6 == 6, "DivideIt(27) failed";

  var r7 := DivideIt(1000000000000000000);
  expect r7 == 72, "DivideIt(1000000000000000000) failed";

  // Test 2
  var r8 := DivideIt(22876792454961);
  expect r8 == 56, "DivideIt(22876792454961) failed";

  // Test 3
  var r9 := DivideIt(70745089028899904);
  expect r9 == -1, "DivideIt(70745089028899904) failed";

  // Test 4
  var r10 := DivideIt(576460752303423487);
  expect r10 == -1, "DivideIt(576460752303423487) failed";

  // Test 5
  var r11 := DivideIt(1);
  expect r11 == 0, "DivideIt(1) [test5] failed";

  // Test 6
  var r12 := DivideIt(30);
  expect r12 == 6, "DivideIt(30) [test6] failed";

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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0102_1176_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0102_1176_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0102_1176_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0102_1176_A/ (create the directory if needed).
