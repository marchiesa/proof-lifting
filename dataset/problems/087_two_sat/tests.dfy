// 2-SAT -- Test cases

method {:axiom} TwoSAT(nVars: int, clauses: seq<(int, int)>) returns (sat: bool, assignment: seq<bool>)
  requires nVars > 0
  requires forall k :: 0 <= k < |clauses| ==> 
    -nVars <= clauses[k].0 && clauses[k].0 <= nVars && clauses[k].0 != 0 &&
    -nVars <= clauses[k].1 && clauses[k].1 <= nVars && clauses[k].1 != 0
  ensures |assignment| == nVars

method TestSimple()
{
  // (x1 or x2) and (-x1 or x2) => x2 must be true
  var sat, asgn := TwoSAT(2, [(1, 2), (-1, 2)]);
  assert |asgn| == 2;
}
