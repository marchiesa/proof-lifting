// ============================================================================
// A3 — Z3 Does Not Search for Existential Witnesses
//
// Z3 is a refutation solver. To prove `exists x :: P(x)` it negates the goal
// to `forall x :: !P(x)`, introduces a Skolem constant x_sk, and looks for a
// contradiction. It never enumerates candidate values for x.
//
// The fix is always the same: assert a concrete witness so that the ground
// term P(witness) enters the e-graph and the definition axiom fires.
// ============================================================================


// ---------------------------------------------------------------------------
// W1: trivially satisfied predicate
//
// Small(x) holds for every x in the stated range. The witness is the entire
// domain. Z3 still will not find one.
// ---------------------------------------------------------------------------

ghost predicate Small(x: nat)
{
  x <= 10
}

// Fails: Z3 does not try any value for x.
lemma SmallExists_Fails()
  ensures exists x: nat | 0 <= x <= 10 :: Small(x)
{
}

// Fix: name a concrete witness.
lemma SmallExists_Fix()
  ensures exists x: nat | 0 <= x <= 10 :: Small(x)
{
  assert Small(0);
}


// ---------------------------------------------------------------------------
// W2: finite two-value domain
//
// Match is a predicate over bool; only two possible witnesses exist.
// Z3 still does not try flag = false or flag = true.
// ---------------------------------------------------------------------------

ghost predicate Match(a: int, b: int, flag: bool)
{
  if flag then a == b + 1 else a == b - 1
}

// Fails: Z3 does not enumerate flag ∈ {false, true}.
lemma MatchExists_Fails(a: int, b: int)
  requires a == b + 1
  ensures exists flag: bool :: Match(a, b, flag)
{
}

// Fix: assert at the concrete witness.
lemma MatchExists_Fix(a: int, b: int)
  requires a == b + 1
  ensures exists flag: bool :: Match(a, b, flag)
{
  assert Match(a, b, true);
}

// Contrast: a hypothesis already in scope provides the ground term — no hint needed.
lemma MatchExists_NoHint(a: int, b: int, flag: bool)
  requires Match(a, b, flag)
  ensures exists f: bool :: Match(a, b, f)
{
}


// ---------------------------------------------------------------------------
// W3: witness requires a case split
//
// Neither witness is universally valid; the proof must branch and assert the
// appropriate one in each branch.
// ---------------------------------------------------------------------------

ghost predicate BetterSide(x: int, y: int, chooseX: bool)
{
  if chooseX then x >= y else y >= x
}

// Fails: Z3 cannot choose between true and false without help.
lemma PickBetter_Fails(x: int, y: int)
  ensures exists choice: bool :: BetterSide(x, y, choice)
{
}

// Fix: assert the right witness in each branch.
lemma PickBetter_Fix(x: int, y: int)
  ensures exists choice: bool :: BetterSide(x, y, choice)
{
  if x >= y {
    assert BetterSide(x, y, true);
  } else {
    assert BetterSide(x, y, false);
  }
}


// ---------------------------------------------------------------------------
// W4: open-ended arithmetic predicate
//
// IsTriangle has three conjuncts. Z3 has no mechanism to search for a triple
// satisfying all three simultaneously.
// ---------------------------------------------------------------------------

ghost predicate IsTriangle(x: int, y: int, z: int)
{
  x + y > z && x + z > y && y + z > x
}

// Fails: Z3 does not search for a satisfying triple.
lemma ConstructTriangle_Fails()
  ensures exists x, y, z :: IsTriangle(x, y, z)
{
}

// Fix: name a concrete witness.
lemma ConstructTriangle_Fix()
  ensures exists x, y, z :: IsTriangle(x, y, z)
{
  assert IsTriangle(2, 2, 1);
}
