// ============================================================================
// A4 — Universal Fact Not Synthesized from Individual Element Facts
//
// Z3 does not generalize from ground facts to universally quantified
// statements. After a sequence update, each element fact is derivable at
// any specific index, but the solver will not produce a forall automatically.
// An explicit `assert forall` or ghost `forall` statement is required.
// ============================================================================


// ---------------------------------------------------------------------------
// U1: forall bridge after conditional sequence append
//
// The loop invariant says every positive value seen so far has a witness in
// `result`. After a conditional append (`if a[k] > 0 { result := result + [a[k]] }`),
// old witnesses (indices into `prev`) still work — but only if the solver
// knows that `result[j] == prev[j]` for all old indices j.
//
// Z3 can verify `result[j'] == prev[j']` at any *specific* j'. But it will
// not derive the universal `forall j :: result[j] == prev[j]` automatically,
// so it cannot propagate the old existential witnesses to the new `result`.
// ---------------------------------------------------------------------------

// Fails: invariant cannot be re-established — old witnesses are lost.
method Filter_Fails(a: seq<int>) returns (result: seq<int>)
  ensures forall i | 0 <= i < |a| :: a[i] > 0 ==>
                                       exists j | 0 <= j < |result| :: result[j] == a[i]
{
  result := [];
  var k := 0;
  while k < |a|
    invariant 0 <= k <= |a|
    invariant forall i | 0 <= i < k :: a[i] > 0 ==>
                                         exists j | 0 <= j < |result| :: result[j] == a[i]
  {
    ghost var prev := result;
    if a[k] > 0 { result := result + [a[k]]; }
    assert result[..|prev|] == prev;
    assert multiset(prev) <= multiset(result);
    k := k + 1;
  }
}

// Fix: ghost forall statement explicitly provides the universal bridge.
method Filter_Fix(a: seq<int>) returns (result: seq<int>)
  ensures forall i | 0 <= i < |a| :: a[i] > 0 ==>
                                       exists j | 0 <= j < |result| :: result[j] == a[i]
{
  result := [];
  var k := 0;
  while k < |a|
    invariant 0 <= k <= |a|
    invariant forall i | 0 <= i < k :: a[i] > 0 ==>
                                         exists j | 0 <= j < |result| :: result[j] == a[i]
  {
    ghost var prev := result;
    if a[k] > 0 { result := result + [a[k]]; }

    // A4: prove the universal preservation fact.
    // For each old i with a[i] > 0, extract the old witness j' from prev,
    // then assert result[j'] == prev[j'] — this places result[j'] in the
    // e-graph and fires the sequence-append axiom at the specific index j'.
    // The solver can then re-establish the existential for each i.
    forall i | 0 <= i < k && a[i] > 0
      ensures exists j | 0 <= j < |result| :: result[j] == a[i]
    {
      var j' :| 0 <= j' < |prev| && prev[j'] == a[i];
      assert result[j'] == prev[j'];   // A4: ground term fires append axiom
    }

    // Witness for the new element (index k).
    if a[k] > 0 { assert result[|prev|] == a[k]; }
    k := k + 1;
  }
}
