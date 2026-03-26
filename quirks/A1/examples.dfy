
predicate P(x: nat)

function f(n: nat): nat
{
  n+1
}
function g(n: nat): nat
{
  n+1
}

lemma Obvious1(n: nat, m: nat)
  requires exists k | n <= k < m :: P(f(k))
  ensures exists k | n <= k < m :: P(g(k))
{
  // Fails without these, any one of the assertions is sufficient:
  // assert exists k {:trigger f(k)} | n <= k < m :: P(g(k));
  assert exists k | n <= k < m :: P(g(k)) by {
    var k :| n <= k < m && P(f(k));
    assert P(g(k));
  }
}
lemma Obvious2(n: nat, m: nat)
  requires exists k | n <= k < m :: P(f(k))
  ensures exists k | n <= k < m+1 :: P(k)
{
  //This one verifies automatically
}
method index_offset(s: seq<nat>)
  requires exists k | 1 <= k < |s| :: P(s[k])
  ensures exists k {:trigger s[k+1]} | 0 <= k < |s|-1 :: P(s[k+1])
{
  // Fails without explicitly constructing a witness.
  var k :| 1 <= k < |s| && P(s[k]);
  var k' := k-1;
  var _ :=  P(s[k'+1]);
}


// ---------------------------------------------------------------------------
// Realistic example: find the last row of a grid containing value v.
// Returns an exclusive upper bound `bottom`: the last marked row is grid[bottom-1].
//
// The quirk arises from a necessary naming split:
//   - the loop uses scalar variable `bot` as the current row index, which
//     gives Z3 a trigger-friendly term in the invariant: grid[bot][c]
//   - after the loop, `bottom := bot + 1` introduces the exclusive-end convention
//     expected by callers, but now the postcondition uses grid[bottom-1][c]
//
// bot == bottom - 1 holds, but grid[bot][c_sk] and grid[bottom-1][c_sk] are
// in different e-graph nodes. The Skolem witness c_sk (from the invariant
// existential) gives Z3 `grid[bot][c_sk] == v`, but the postcondition trigger
// fires on `grid[bottom-1][c]` — a term that was never produced as a ground
// fact — so the proof stalls.
// ---------------------------------------------------------------------------

// Fails: postcondition cannot be proved.
method FindLastRow_Fails(grid: seq<seq<int>>, v: int) returns (bottom: nat)
  requires |grid| > 0
  requires exists r | 0 <= r < |grid| :: exists c | 0 <= c < |grid[r]| :: grid[r][c] == v
  ensures 0 < bottom <= |grid|
  ensures exists c {:trigger grid[bottom - 1][c]} | 0 <= c < |grid[bottom - 1]| :: grid[bottom - 1][c] == v
{
  var bot := |grid| - 1;
  var botDone := false;
  while !botDone
    invariant 0 <= bot < |grid|
    invariant !botDone ==>
                exists r | 0 <= r <= bot :: exists c | 0 <= c < |grid[r]| :: grid[r][c] == v
    invariant botDone ==>
                exists c | 0 <= c < |grid[bot]| :: grid[bot][c] == v   // uses grid[bot]
    decreases bot + 1, !botDone
  {
    if exists c | 0 <= c < |grid[bot]| :: grid[bot][c] == v {
      botDone := true;
    } else {
      assert exists r | 0 <= r < bot :: exists c | 0 <= c < |grid[r]| :: grid[r][c] == v;
      bot := bot - 1;
    }
  }
  bottom := bot + 1;
  // grid[bot][c_sk] is in the e-graph (Skolem witness from invariant),
  // but the trigger {:trigger grid[bottom-1][c]} never fires because
  // grid[bottom-1][c_sk] has not been produced as a ground term.
} // <-- postcondition error here

// Fix 1 — by-body: manually Skolemise the invariant existential.
// Naming c0 forces grid[bot][c0] into the e-graph as a ground fact;
// `assert grid[bottom-1][c0] == v` then follows by congruence (bot == bottom-1).
method FindLastRow_Fix1(grid: seq<seq<int>>, v: int) returns (bottom: nat)
  requires |grid| > 0
  requires exists r | 0 <= r < |grid| :: exists c | 0 <= c < |grid[r]| :: grid[r][c] == v
  ensures 0 < bottom <= |grid|
  ensures exists c {:trigger grid[bottom - 1][c]} | 0 <= c < |grid[bottom - 1]| :: grid[bottom - 1][c] == v
{
  var bot := |grid| - 1;
  var botDone := false;
  while !botDone
    invariant 0 <= bot < |grid|
    invariant !botDone ==>
                exists r | 0 <= r <= bot :: exists c | 0 <= c < |grid[r]| :: grid[r][c] == v
    invariant botDone ==>
                exists c | 0 <= c < |grid[bot]| :: grid[bot][c] == v
    decreases bot + 1, !botDone
  {
    if exists c | 0 <= c < |grid[bot]| :: grid[bot][c] == v {
      botDone := true;
    } else {
      assert exists r | 0 <= r < bot :: exists c | 0 <= c < |grid[r]| :: grid[r][c] == v;
      bot := bot - 1;
    }
  }
  bottom := bot + 1;
  assert exists c {:trigger grid[bottom - 1][c]} | 0 <= c < |grid[bottom - 1]| :: grid[bottom - 1][c] == v by {
    var c0 :| 0 <= c0 < |grid[bot]| && grid[bot][c0] == v;  // Skolemise
    assert grid[bottom - 1][c0] == v;                        // congruence: bot == bottom - 1
  }
}

// Fix 2 — trigger trick: use grid[bot][c] as the trigger instead of grid[bottom-1][c].
// E-matching fires on grid[bot][c_sk] (which IS in the e-graph from the Skolemised
// invariant), and congruence closure (bot == bottom-1) then establishes the body.
// Counter-intuitive: the trigger does not appear in the formula body, yet it works.
method FindLastRow_Fix2(grid: seq<seq<int>>, v: int) returns (bottom: nat)
  requires |grid| > 0
  requires exists r | 0 <= r < |grid| :: exists c | 0 <= c < |grid[r]| :: grid[r][c] == v
  ensures 0 < bottom <= |grid|
  ensures exists c {:trigger grid[bottom - 1][c]} | 0 <= c < |grid[bottom - 1]| :: grid[bottom - 1][c] == v
{
  var bot := |grid| - 1;
  var botDone := false;
  while !botDone
    invariant 0 <= bot < |grid|
    invariant !botDone ==>
                exists r | 0 <= r <= bot :: exists c | 0 <= c < |grid[r]| :: grid[r][c] == v
    invariant botDone ==>
                exists c | 0 <= c < |grid[bot]| :: grid[bot][c] == v
    decreases bot + 1, !botDone
  {
    if exists c | 0 <= c < |grid[bot]| :: grid[bot][c] == v {
      botDone := true;
    } else {
      assert exists r | 0 <= r < bot :: exists c | 0 <= c < |grid[r]| :: grid[r][c] == v;
      bot := bot - 1;
    }
  }
  bottom := bot + 1;
  assert exists c {:trigger grid[bot][c]} | 0 <= c < |grid[bottom - 1]| :: grid[bottom - 1][c] == v;
}