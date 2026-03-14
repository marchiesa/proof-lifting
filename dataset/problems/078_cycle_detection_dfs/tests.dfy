// Cycle Detection -- Test cases

method {:axiom} HasCycle(graph: seq<seq<bool>>, n: int) returns (hasCycle: bool)
  requires n >= 0
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n

method TestNoCycle()
{
  var g := [[false, true, false], [false, false, true], [false, false, false]];
  var c := HasCycle(g, 3);
}

method TestWithCycle()
{
  var g := [[false, true, false], [false, false, true], [true, false, false]];
  var c := HasCycle(g, 3);
}
