// 2-SAT Satisfiability
// Task: Add loop invariants so that Dafny can verify this program.
// Simplified: uses iterative unit propagation approach

method TwoSAT(nVars: int, clauses: seq<(int, int)>) returns (sat: bool, assignment: seq<bool>)
  requires nVars > 0
  requires forall k :: 0 <= k < |clauses| ==> 
    -nVars <= clauses[k].0 && clauses[k].0 <= nVars && clauses[k].0 != 0 &&
    -nVars <= clauses[k].1 && clauses[k].1 <= nVars && clauses[k].1 != 0
  ensures |assignment| == nVars
{
  assignment := seq(nVars, _ => false);
  // Try all 2^n assignments (brute force for small n, bounded by fuel)
  var fuel := if nVars <= 20 then 1 else 0;
  var attempt := 0;
  sat := false;
  while attempt < fuel
  {
    // Check current assignment against all clauses
    var allSat := true;
    var c := 0;
    while c < |clauses|
    {
      var l1 := clauses[c].0;
      var l2 := clauses[c].1;
      var v1 := if l1 > 0 then assignment[l1 - 1] else !assignment[-l1 - 1];
      var v2 := if l2 > 0 then assignment[l2 - 1] else !assignment[-l2 - 1];
      if !v1 && !v2 {
        allSat := false;
      }
      c := c + 1;
    }
    if allSat {
      sat := true;
      return;
    }
    // Increment assignment
    var carry := true;
    var bit := 0;
    while bit < nVars && carry
    {
      if !assignment[bit] {
        assignment := assignment[bit := true];
        carry := false;
      } else {
        assignment := assignment[bit := false];
      }
      bit := bit + 1;
    }
    if carry { break; }
    attempt := attempt + 1;
  }
}
