// ============================================================================
// A2 — Predicate Definition Not Applied Without Explicit Instantiation
// ============================================================================


// ---------------------------------------------------------------------------
// Example 1: boolean witness
//
// Match is a predicate over bool; only two witnesses exist.
// Proving the existential still requires an explicit predicate assertion.
// ---------------------------------------------------------------------------

predicate P(x: nat)
{
  x == 4
}

ghost predicate Match(a: int, b: int, flag: bool)
{
  if flag then a == b + 1 else a == b - 1
}

// Fails: Z3 does not enumerate flag ∈ {false, true} to find a witness.
lemma ShowExists_Fails(a: int, b: int)
  requires a == b + 1
  ensures exists flag: bool :: Match(a, b, flag)
{
  // Without any hint, Dafny reports "postcondition could not be proved"
}

// Fix: explicitly assert the predicate at the concrete witness.
lemma ShowExists_Fix(a: int, b: int)
  requires a == b + 1
  ensures exists flag: bool :: Match(a, b, flag)
{
  assert Match(a, b, true);  // places Match(a, b, true) in e-graph; done
}

// Contrast: when the predicate term already appears in a hypothesis, no hint needed.
lemma ShowExists_NoHintNeeded(a: int, b: int, flag: bool)
  requires Match(a, b, flag)               // Match(a,b,flag) already in e-graph
  ensures exists f: bool :: Match(a, b, f)
{
  // Verifies automatically: the hypothesis places Match(a,b,flag) as a ground term.
}


// ---------------------------------------------------------------------------
// Example 2: compound arithmetic predicate
//
// IsTriangle has three conjuncts. Proving the existential `exists x, y, z ::
// IsTriangle(x, y, z)` requires placing a concrete predicate ground term in
// the e-graph; Z3 will not search for a satisfying instantiation on its own.
// ---------------------------------------------------------------------------

ghost predicate IsTriangle(x: int, y: int, z: int)
{
  x + y > z && x + z > y && y + z > x
}

// Fails: Z3 needs a ground term IsTriangle(?, ?, ?) to instantiate the existential.
lemma ConstructTriangle_Fails()
  ensures exists x, y, z :: IsTriangle(x, y, z)
{
  // No explicit witness; Z3 does not search for one.
}

// Fix: assert the predicate at a concrete witness.
lemma ConstructTriangle_Fix()
  ensures exists x, y, z :: IsTriangle(x, y, z)
{
  assert IsTriangle(2, 2, 1);   // 2+2>1, 2+1>2, 2+1>2; now the existential fires
}


// ---------------------------------------------------------------------------
// Example 3: case-split proof — predicate asserted in each branch
//
// To prove an existential over bool, split on the case and assert the
// concrete predicate instance in each branch.
// ---------------------------------------------------------------------------

ghost predicate BetterSide(x: int, y: int, chooseX: bool)
{
  if chooseX then x >= y else y >= x
}

// Fails: Dafny cannot find a witness for the bool existential without a hint.
lemma PickBetter_Fails(x: int, y: int)
  ensures exists choice: bool :: BetterSide(x, y, choice)
{
  // No help given; both BetterSide(x, y, true) and BetterSide(x, y, false)
  // are absent from the e-graph.
}

// Fix: assert in each branch so Z3 has a ground term to use as witness.
lemma PickBetter_Fix(x: int, y: int)
  ensures exists choice: bool :: BetterSide(x, y, choice)
{
  if x >= y {
    assert BetterSide(x, y, true);
  } else {
    assert BetterSide(x, y, false);
  }
}

function add(x: int, y: int): int
{
  x + y
}

lemma tmp(x: int, y: int)
  // ensures exists z: int {:trigger y} :: x + z == y
  ensures exists z :: add(x, z) == y
{
  assert add(x, y-x) == y;
}

predicate Holder(x: int)

lemma tmp2(x: int, y: int)
  ensures exists z: int {:trigger Holder(z)} :: x + z == y
{
  // assert x + (y-x) == y;
  var _ := Holder(y-x);
}