// 2-SAT -- Runtime spec tests

// The spec: ensures |assignment| == nVars
// We test this postcondition and the clause satisfaction checker.

method CheckAssignmentSpec(assignment: seq<bool>, nVars: int) returns (ok: bool)
{
  ok := |assignment| == nVars;
}

// Check if an assignment satisfies all clauses
method CheckSatisfied(nVars: int, clauses: seq<(int, int)>, assignment: seq<bool>) returns (ok: bool)
  requires nVars > 0
  requires |assignment| == nVars
  requires forall k :: 0 <= k < |clauses| ==>
    -nVars <= clauses[k].0 && clauses[k].0 <= nVars && clauses[k].0 != 0 &&
    -nVars <= clauses[k].1 && clauses[k].1 <= nVars && clauses[k].1 != 0
{
  var c := 0;
  while c < |clauses|
  {
    var l1 := clauses[c].0;
    var l2 := clauses[c].1;
    var v1 := if l1 > 0 then assignment[l1 - 1] else !assignment[-l1 - 1];
    var v2 := if l2 > 0 then assignment[l2 - 1] else !assignment[-l2 - 1];
    if !v1 && !v2 { return false; }
    c := c + 1;
  }
  return true;
}

// Check precondition validity
method ValidClausesCheck(nVars: int, clauses: seq<(int, int)>) returns (ok: bool)
{
  if nVars <= 0 { return false; }
  var k := 0;
  while k < |clauses|
  {
    var l1 := clauses[k].0;
    var l2 := clauses[k].1;
    if l1 < -nVars || l1 > nVars || l1 == 0 { return false; }
    if l2 < -nVars || l2 > nVars || l2 == 0 { return false; }
    k := k + 1;
  }
  return true;
}

method Main()
{
  // Test postcondition: |assignment| == nVars
  var ok := CheckAssignmentSpec([true, false], 2);
  expect ok, "|assignment|=2 matches nVars=2";

  ok := CheckAssignmentSpec([true], 1);
  expect ok, "|assignment|=1 matches nVars=1";

  ok := CheckAssignmentSpec([true, false, true], 3);
  expect ok, "|assignment|=3 matches nVars=3";

  // Negative: wrong length
  ok := CheckAssignmentSpec([true], 2);
  expect !ok, "|assignment|=1 != nVars=2";

  ok := CheckAssignmentSpec([true, false], 1);
  expect !ok, "|assignment|=2 != nVars=1";

  // Test clause satisfaction checker
  // (x1 or x2) with x1=true, x2=false => satisfied
  var r := CheckSatisfied(2, [(1, 2)], [true, false]);
  expect r, "(x1 or x2) with [T,F] should be satisfied";

  // (x1 or x2) and (-x1 or x2) with x1=true, x2=true => satisfied
  r := CheckSatisfied(2, [(1, 2), (-1, 2)], [true, true]);
  expect r, "(x1 or x2)(not x1 or x2) with [T,T] should be satisfied";

  // (x1 or x2) and (-x1 or x2) with x1=true, x2=false => not satisfied
  r := CheckSatisfied(2, [(1, 2), (-1, 2)], [true, false]);
  expect !r, "(x1 or x2)(not x1 or x2) with [T,F] should NOT be satisfied";

  // (x1 or x1) => x1 must be true
  r := CheckSatisfied(1, [(1, 1)], [true]);
  expect r, "(x1 or x1) with [T] should be satisfied";
  r := CheckSatisfied(1, [(1, 1)], [false]);
  expect !r, "(x1 or x1) with [F] should NOT be satisfied";

  // No clauses => always satisfied
  r := CheckSatisfied(2, [], [false, false]);
  expect r, "No clauses: always satisfied";

  // Test clause validation
  r := ValidClausesCheck(2, [(1, 2), (-1, 2)]);
  expect r, "Valid clauses for nVars=2";

  r := ValidClausesCheck(2, [(1, 3)]);
  expect !r, "Literal 3 out of range for nVars=2";

  r := ValidClausesCheck(2, [(0, 1)]);
  expect !r, "Literal 0 is invalid";

  r := ValidClausesCheck(0, []);
  expect !r, "nVars=0 is invalid";

  print "All spec tests passed\n";
}
