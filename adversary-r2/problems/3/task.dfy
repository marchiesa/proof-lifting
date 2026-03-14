// Problem 3: Edit Distance (Levenshtein) with Optimality Proof
//
// Compute the minimum edit distance between two sequences.
// Operations: insert, delete, replace (each cost 1).
//
// The spec requires OPTIMALITY: no edit sequence has lower cost.

// Edit operations
datatype EditOp =
  | Insert(pos: nat, ch: int)      // Insert ch at position pos
  | Delete(pos: nat)                // Delete character at position pos
  | Replace(pos: nat, ch: int)     // Replace character at position pos with ch

// Apply a single edit operation to a sequence
ghost function ApplyOp(s: seq<int>, op: EditOp): seq<int>
  requires op.Insert? ==> op.pos <= |s|
  requires op.Delete? ==> op.pos < |s|
  requires op.Replace? ==> op.pos < |s|
{
  match op
  case Insert(pos, ch) => s[..pos] + [ch] + s[pos..]
  case Delete(pos) => s[..pos] + s[pos + 1..]
  case Replace(pos, ch) => s[..pos] + [ch] + s[pos + 1..]
}

// A valid edit sequence: each operation is valid for the intermediate string
ghost predicate ValidEditSequence(s: seq<int>, ops: seq<EditOp>, t: seq<int>)
  decreases |ops|
{
  if |ops| == 0 then
    s == t
  else
    var op := ops[0];
    (match op
     case Insert(pos, ch) => pos <= |s|
     case Delete(pos) => pos < |s|
     case Replace(pos, ch) => pos < |s|) &&
    ValidEditSequence(ApplyOp(s, op), ops[1..], t)
}

// The cost of an edit sequence is simply its length
ghost function EditCost(ops: seq<EditOp>): nat
{
  |ops|
}

// OPTIMALITY spec: the returned distance is the minimum edit cost
ghost predicate IsMinEditDistance(s: seq<int>, t: seq<int>, dist: nat)
{
  // 1. There exists an edit sequence of this cost
  (exists ops: seq<EditOp> :: ValidEditSequence(s, ops, t) && EditCost(ops) == dist) &&
  // 2. No edit sequence has lower cost
  (forall ops: seq<EditOp> :: ValidEditSequence(s, ops, t) ==> EditCost(ops) >= dist)
}

// Helper: min of two nats
function Min2(a: nat, b: nat): nat
{
  if a <= b then a else b
}

// Helper: min of three nats
function Min3(a: nat, b: nat, c: nat): nat
{
  Min2(a, Min2(b, c))
}

// Main method: Edit Distance via bottom-up 2D DP
method EditDistance(s: seq<int>, t: seq<int>) returns (dist: nat)
  ensures IsMinEditDistance(s, t, dist)
{
  var m := |s|;
  var n := |t|;

  // dp[i][j] = edit distance between s[..i] and t[..j]
  var dp := new nat[m + 1, n + 1];

  // Base cases
  var i := 0;
  while i <= m
  {
    dp[i, 0] := i;  // delete all characters from s[..i]
    i := i + 1;
  }
  var j := 0;
  while j <= n
  {
    dp[0, j] := j;  // insert all characters of t[..j]
    j := j + 1;
  }

  // Fill DP table
  i := 1;
  while i <= m
  {
    j := 1;
    while j <= n
    {
      if s[i - 1] == t[j - 1] {
        dp[i, j] := dp[i - 1, j - 1];
      } else {
        dp[i, j] := 1 + Min3(
          dp[i - 1, j],      // delete
          dp[i, j - 1],      // insert
          dp[i - 1, j - 1]   // replace
        );
      }
      j := j + 1;
    }
    i := i + 1;
  }

  dist := dp[m, n];
}
