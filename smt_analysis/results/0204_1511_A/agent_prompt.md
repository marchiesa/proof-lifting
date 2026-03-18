Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Review Site
You are an upcoming movie director, and you have just released your first movie. You have also launched a simple review site with two buttons to press — upvote and downvote.

However, the site is not so simple on the inside. There are two servers, each with its separate counts for the upvotes and the downvotes.

$$$n$$$ reviewers enter the site one by one. Each reviewer is one of the following types:

- type $$$1$$$: a reviewer has watched the movie, and they like it — they press the upvote button;
- type $$$2$$$: a reviewer has watched the movie, and they dislike it — they press the downvote button;
- type $$$3$$$: a reviewer hasn't watched the movie — they look at the current number of upvotes and downvotes of the movie on the server they are in and decide what button to press. If there are more downvotes than upvotes, then a reviewer downvotes the movie. Otherwise, they upvote the movie.

Each reviewer votes on the movie exactly once.

Since you have two servers, you can actually manipulate the votes so that your movie gets as many upvotes as possible. When a reviewer enters a site, you know their type, and you can send them either to the first server or to the second one.

What is the maximum total number of upvotes you can gather over both servers if you decide which server to send each reviewer to?

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0204_1511_A/task.dfy

```dafny
datatype ServerState = ServerState(up1: int, down1: int, up2: int, down2: int)

// Models one reviewer voting: type 1 upvotes, type 2 downvotes,
// type 3 checks the server's current counts (downvotes > upvotes → downvote, else upvote)
ghost function ProcessReviewer(state: ServerState, reviewerType: int, goToServer2: bool): ServerState
{
  if !goToServer2 then
    if reviewerType == 1 then ServerState(state.up1 + 1, state.down1, state.up2, state.down2)
    else if reviewerType == 2 then ServerState(state.up1, state.down1 + 1, state.up2, state.down2)
    else if state.down1 > state.up1 then ServerState(state.up1, state.down1 + 1, state.up2, state.down2)
    else ServerState(state.up1 + 1, state.down1, state.up2, state.down2)
  else
    if reviewerType == 1 then ServerState(state.up1, state.down1, state.up2 + 1, state.down2)
    else if reviewerType == 2 then ServerState(state.up1, state.down1, state.up2, state.down2 + 1)
    else if state.down2 > state.up2 then ServerState(state.up1, state.down1, state.up2, state.down2 + 1)
    else ServerState(state.up1, state.down1, state.up2 + 1, state.down2)
}

// Simulate all reviewers in order; each bit of mask assigns the corresponding reviewer to a server
ghost function Simulate(r: seq<int>, mask: int): ServerState
  requires mask >= 0
  decreases |r|
{
  if |r| == 0 then ServerState(0, 0, 0, 0)
  else
    var prev := Simulate(r[..|r|-1], mask / 2);
    ProcessReviewer(prev, r[|r|-1], mask % 2 == 1)
}

// Total upvotes across both servers for a given server-assignment mask
ghost function TotalUpvotes(r: seq<int>, mask: int): int
  requires mask >= 0
{
  var s := Simulate(r, mask);
  s.up1 + s.up2
}

ghost function Pow2(n: int): int
  requires n >= 0
  ensures Pow2(n) >= 1
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

// Maximum total upvotes over all assignment masks from 0 to bound (inclusive)
ghost function MaxUpvotesOver(r: seq<int>, bound: int): int
  requires bound >= 0
  decreases bound
{
  var curr := TotalUpvotes(r, bound);
  if bound == 0 then curr
  else
    var prev := MaxUpvotesOver(r, bound - 1);
    if curr > prev then curr else prev
}

// The optimal total upvotes achievable over all possible server assignment strategies
ghost function BestUpvotes(r: seq<int>): int
{
  MaxUpvotesOver(r, Pow2(|r|) - 1)
}

method ReviewSite(n: int, r: seq<int>) returns (maxUpvotes: int)
  requires n == |r|
  requires forall i | 0 <= i < |r| :: r[i] == 1 || r[i] == 2 || r[i] == 3
  ensures maxUpvotes == BestUpvotes(r)
{
  var count := 0;
  var i := 0;
  while i < |r|
  {
    if r[i] == 1 || r[i] == 3 {
      count := count + 1;
    }
    i := i + 1;
  }
  return count;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0204_1511_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0204_1511_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0204_1511_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0204_1511_A/ (create the directory if needed).
