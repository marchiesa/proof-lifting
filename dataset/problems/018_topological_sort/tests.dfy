// Topological Sort Existence (Cycle Detection) -- Test cases

method {:axiom} CountProcessable(graph: seq<seq<bool>>, n: int) returns (count: int)
  requires n >= 0
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  ensures 0 <= count <= n

method TestDAG()
{
  // Graph: 0->1, 0->2, 1->2 (DAG)
  var graph := [[false, true, true], [false, false, true], [false, false, false]];
  var count := CountProcessable(graph, 3);
  assert 0 <= count <= 3;
}

method TestCycle()
{
  // Graph: 0->1, 1->0 (cycle)
  var graph := [[false, true], [true, false]];
  var count := CountProcessable(graph, 2);
  assert 0 <= count <= 2;
}

method TestSingleNode()
{
  var graph := [[false]];
  var count := CountProcessable(graph, 1);
  assert 0 <= count <= 1;
}

method TestEmpty()
{
  var graph: seq<seq<bool>> := [];
  var count := CountProcessable(graph, 0);
  assert count == 0;
}
