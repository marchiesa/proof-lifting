// Test file for AstMappingManager - demonstrates forall PROOF statements
// (forall statements with ensures clauses that prove quantified properties)
//
// Verified: 3 verified, 0 errors

predicate AllPositive(s: seq<int>)
{
  forall i :: 0 <= i < |s| ==> s[i] > 0
}

method TestForallProof(s: seq<int>)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
{
  // Forall PROOF statement - proves a quantified property
  // This is tracked by AstMappingManager because it has an 'ensures' clause
  forall i | 0 <= i < |s|
    ensures s[i] * s[i] > 0
  {
    assert s[i] > 0;  // From precondition
    assert s[i] * s[i] > 0;  // Squares are positive
  }

  // Now we can use the proven property
  assert forall i :: 0 <= i < |s| ==> s[i] * s[i] > 0;
}
