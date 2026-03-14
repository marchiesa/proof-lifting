// Strongly Connected Components (Transitive Closure) -- Runtime spec tests
// The spec is: reach is n x n, reflexive (reach[i][i] == true).
// We test the reflexivity property and valid matrix structure.

predicate ValidBoolMatrix(m: seq<seq<bool>>, n: int)
{
  |m| == n &&
  (forall i | 0 <= i < n :: |m[i]| == n)
}

predicate IsReflexive(m: seq<seq<bool>>, n: int)
  requires ValidBoolMatrix(m, n)
{
  forall i | 0 <= i < n :: m[i][i]
}

method Main()
{
  // Test ValidBoolMatrix
  expect ValidBoolMatrix([[true, false], [false, true]], 2), "2x2 bool matrix valid";
  expect ValidBoolMatrix([[false]], 1), "1x1 bool matrix valid";
  expect ValidBoolMatrix([], 0), "empty matrix valid for n=0";
  expect !ValidBoolMatrix([[true, false], [true]], 2), "ragged matrix not valid";

  // Test IsReflexive
  var id2 := [[true, false], [false, true]];
  expect ValidBoolMatrix(id2, 2) && IsReflexive(id2, 2), "identity matrix is reflexive";

  var full2 := [[true, true], [true, true]];
  expect ValidBoolMatrix(full2, 2) && IsReflexive(full2, 2), "full matrix is reflexive";

  var notRefl := [[false, true], [true, false]];
  expect ValidBoolMatrix(notRefl, 2) && !IsReflexive(notRefl, 2),
    "anti-diagonal is not reflexive";

  // Test a known transitive closure result
  // Graph: 0->1, 1->2 (linear chain)
  // Transitive closure should be:
  // reach[0][0]=T, reach[0][1]=T, reach[0][2]=T (0 can reach all)
  // reach[1][0]=F, reach[1][1]=T, reach[1][2]=T (1 can reach 1,2)
  // reach[2][0]=F, reach[2][1]=F, reach[2][2]=T (2 can only reach 2)
  var tcChain := [[true, true, true], [false, true, true], [false, false, true]];
  expect ValidBoolMatrix(tcChain, 3), "chain TC has valid structure";
  expect IsReflexive(tcChain, 3), "chain TC is reflexive";
  expect tcChain[0][1], "0 can reach 1";
  expect tcChain[0][2], "0 can reach 2";
  expect !tcChain[1][0], "1 cannot reach 0";
  expect !tcChain[2][0], "2 cannot reach 0";

  // Test a cycle: 0->1, 1->0
  // TC: all true
  var tcCycle := [[true, true], [true, true]];
  expect ValidBoolMatrix(tcCycle, 2) && IsReflexive(tcCycle, 2), "cycle TC is reflexive";
  expect tcCycle[0][1] && tcCycle[1][0], "both directions reachable in cycle";

  print "All spec tests passed\n";
}
