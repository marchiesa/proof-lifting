Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Alexey and Train
Alexey is travelling on a train. Unfortunately, due to the bad weather, the train moves slower that it should!

Alexey took the train at the railroad terminal. Let's say that the train starts from the terminal at the moment $$$0$$$. Also, let's say that the train will visit $$$n$$$ stations numbered from $$$1$$$ to $$$n$$$ along its way, and that Alexey destination is the station $$$n$$$.

Alexey learned from the train schedule $$$n$$$ integer pairs $$$(a_i, b_i)$$$ where $$$a_i$$$ is the expected time of train's arrival at the $$$i$$$-th station and $$$b_i$$$ is the expected time of departure.

Also, using all information he has, Alexey was able to calculate $$$n$$$ integers $$$tm_1, tm_2, \dots, tm_n$$$ where $$$tm_i$$$ is the extra time the train need to travel from the station $$$i - 1$$$ to the station $$$i$$$. Formally, the train needs exactly $$$a_i - b_{i-1} + tm_i$$$ time to travel from station $$$i - 1$$$ to station $$$i$$$ (if $$$i = 1$$$ then $$$b_0$$$ is the moment the train leave the terminal, and it's equal to $$$0$$$).

The train leaves the station $$$i$$$, if both conditions are met:

1. it's on the station for at least $$$\left\lceil \frac{b_i - a_i}{2} \right\rceil$$$ units of time (division with ceiling);
2. current time $$$\ge b_i$$$.

Since Alexey spent all his energy on prediction of time delays, help him to calculate the time of arrival at the station $$$n$$$.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0200_1501_A/task.dfy

```dafny
// ── Specification: Alexey and Train ──

// Input validity: formalizes the problem's constraints on inputs.
ghost predicate ValidInput(n: int, schedule: seq<(int, int)>, tm: seq<int>)
{
  n >= 1 &&
  |schedule| == n &&
  |tm| == n &&
  (forall i | 0 <= i < n :: schedule[i].0 < schedule[i].1) &&
  (forall i | 0 <= i < n :: tm[i] >= 0) &&
  (forall i | 1 <= i < n :: schedule[i - 1].1 < schedule[i].0)
}

// Ceiling of a / 2 for non-negative a.
ghost function CeilDiv2(a: int): int
{
  (a + 1) / 2
}

// The actual arrival time at the last station in the given schedule prefix.
// Models: the train travels exactly (a_i - b_{i-1} + tm_i) time from station i-1 to i,
// where b_0 = 0 (train departs terminal at time 0).
ghost function ArrivalTime(schedule: seq<(int, int)>, tm: seq<int>): int
  requires |schedule| > 0
  requires |tm| == |schedule|
  decreases |schedule|, 0
{
  var n := |schedule|;
  var prevB := if n == 1 then 0 else schedule[n - 2].1;
  var travelTime := schedule[n - 1].0 - prevB + tm[n - 1];
  if n == 1 then
    travelTime
  else
    DepartureTime(schedule[..n - 1], tm[..n - 1]) + travelTime
}

// The actual departure time from the last station in the given schedule prefix.
// Models the two departure conditions from the problem:
//   (1) the train has waited at least ceil((b_i - a_i) / 2) at station i, AND
//   (2) the current time is at least b_i.
// Therefore: departure_i = max(arrival_i + ceil((b_i - a_i) / 2), b_i).
ghost function DepartureTime(schedule: seq<(int, int)>, tm: seq<int>): int
  requires |schedule| > 0
  requires |tm| == |schedule|
  decreases |schedule|, 1
{
  var arrival := ArrivalTime(schedule, tm);
  var n := |schedule|;
  var ai := schedule[n - 1].0;
  var bi := schedule[n - 1].1;
  var minWait := CeilDiv2(bi - ai);
  var earliestDepart := arrival + minWait;
  if earliestDepart >= bi then earliestDepart else bi
}

// ── Implementation ──

method AlexeyAndTrain(n: int, schedule: seq<(int, int)>, tm: seq<int>) returns (arrivalTime: int)
  requires ValidInput(n, schedule, tm)
  ensures arrivalTime == ArrivalTime(schedule, tm)
{
  var currentTime := 0;
  var prevB := 0;
  var i := 0;
  while i < n
  {
    var ai := schedule[i].0;
    var bi := schedule[i].1;
    var travelTime := ai - prevB + tm[i];
    currentTime := currentTime + travelTime;
    if i < n - 1 {
      var waitTime := bi - ai;
      currentTime := currentTime + (waitTime + 1) / 2;
      if currentTime < bi {
        currentTime := bi;
      }
    }
    prevB := bi;
    i := i + 1;
  }
  arrivalTime := currentTime;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0200_1501_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0200_1501_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0200_1501_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0200_1501_A/ (create the directory if needed).
