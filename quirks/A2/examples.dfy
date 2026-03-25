// ============================================================================
// A2 — Universal Quantifier Not Instantiated at Required Arguments
//
// Every use of a predicate's definition — and every use of a universally
// quantified hypothesis — goes through trigger-based quantifier instantiation.
// Z3 fires the axiom only when a matching ground term is present in the e-graph.
//
// The explicit `assert P(args)` is not about the predicate's body being
// "obvious": it places the ground term P(args) in the e-graph so that a
// universally quantified axiom fires at a specific argument.
// ============================================================================


// ---------------------------------------------------------------------------
// T1: firing a forall hypothesis to derive a contradiction
//
// The hypothesis says !Present(k) for all k in [0, n).
// Present(42) is provably true. If n > 42, we have a contradiction — but
// only once Z3 instantiates the forall at k=42.
// The trigger for the forall is Present(k). Without assert Present(42),
// the term Present(42) is never in the e-graph and the trigger never fires.
// ---------------------------------------------------------------------------

ghost predicate Present(x: int)
{
  x == 42
}

// Fails: Present(42) never enters the e-graph; forall trigger at k=42 never fires.
lemma ContradictForall_Fails(n: int)
  requires n > 42
  requires forall k | 0 <= k < n :: !Present(k)
  ensures false
{
}

// Fix: assert Present(42) — fires the trigger, extracts !Present(42), derives false.
lemma ContradictForall_Fix(n: int)
  requires n > 42
  requires forall k | 0 <= k < n :: !Present(k)
  ensures false
{
  assert Present(42);
}

predicate Small(x: nat)
{
  x <= 10
}

lemma ContradictSmall_Fail()
  requires forall x: nat | 0 <= x <= 20 :: Small(x)
  ensures false
{
}

lemma ContradictSmall_Fix()
  requires forall x: nat | 0 <= x <= 20 :: Small(x)
  ensures false
{
  assert Small(19);
}