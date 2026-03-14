// Maximum Bipartite Matching -- Runtime spec tests

// The spec:
//   ensures matchCount <= nLeft
//   ensures matchCount <= nRight
// We test these properties directly.

method CheckMatchingSpec(matchCount: nat, nLeft: int, nRight: int) returns (ok: bool)
{
  ok := matchCount <= nLeft && matchCount <= nRight;
}

method ValidBipartiteInputCheck(graph: seq<seq<bool>>, nLeft: int, nRight: int) returns (ok: bool)
{
  if nLeft < 0 || nRight < 0 { return false; }
  if |graph| != nLeft { return false; }
  var i := 0;
  while i < nLeft
  {
    if |graph[i]| != nRight { return false; }
    i := i + 1;
  }
  return true;
}

method Main()
{
  // Test postcondition: matchCount <= nLeft && matchCount <= nRight
  var ok := CheckMatchingSpec(2, 2, 2);
  expect ok, "matchCount=2 for 2x2: satisfies spec";

  ok := CheckMatchingSpec(0, 2, 2);
  expect ok, "matchCount=0: satisfies spec";

  ok := CheckMatchingSpec(2, 3, 2);
  expect ok, "matchCount=2, nLeft=3, nRight=2: satisfies spec";

  ok := CheckMatchingSpec(1, 1, 5);
  expect ok, "matchCount=1, nLeft=1, nRight=5: satisfies spec";

  ok := CheckMatchingSpec(0, 0, 0);
  expect ok, "matchCount=0, nLeft=0, nRight=0: satisfies spec";

  // Negative: matchCount > nLeft
  ok := CheckMatchingSpec(3, 2, 5);
  expect !ok, "matchCount=3 > nLeft=2: violates spec";

  // Negative: matchCount > nRight
  ok := CheckMatchingSpec(3, 5, 2);
  expect !ok, "matchCount=3 > nRight=2: violates spec";

  // Test precondition validation
  var r := ValidBipartiteInputCheck([[true, false], [false, true]], 2, 2);
  expect r, "Valid 2x2 bipartite graph";

  r := ValidBipartiteInputCheck([[true, false], [false, true], [true, true]], 3, 2);
  expect r, "Valid 3x2 bipartite graph";

  r := ValidBipartiteInputCheck([], 0, 0);
  expect r, "Empty graph is valid";

  r := ValidBipartiteInputCheck([[true]], 2, 1);
  expect !r, "Wrong row count should be invalid";

  r := ValidBipartiteInputCheck([[true, false], [true]], 2, 2);
  expect !r, "Wrong row length should be invalid";

  print "All spec tests passed\n";
}
