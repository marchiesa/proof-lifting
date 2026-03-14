// Strongly Connected Components (Transitive Closure) -- Test cases

method {:axiom} TransitiveClosure(graph: seq<seq<bool>>, n: int) returns (reach: seq<seq<bool>>)
  requires n >= 0
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  ensures |reach| == n
  ensures forall i :: 0 <= i < n ==> |reach[i]| == n
  ensures forall i :: 0 <= i < n ==> reach[i][i]

method TestDAG()
{
  var graph := [[false, true, false], [false, false, true], [false, false, false]];
  var reach := TransitiveClosure(graph, 3);
  assert |reach| == 3;
  assert reach[0][0];
  assert reach[1][1];
  assert reach[2][2];
}

method TestCycle()
{
  var graph := [[false, true], [true, false]];
  var reach := TransitiveClosure(graph, 2);
  assert |reach| == 2;
  assert reach[0][0];
  assert reach[1][1];
}

method TestSingle()
{
  var graph := [[false]];
  var reach := TransitiveClosure(graph, 1);
  assert |reach| == 1;
  assert reach[0][0];
}

method TestEmpty()
{
  var graph: seq<seq<bool>> := [];
  var reach := TransitiveClosure(graph, 0);
  assert |reach| == 0;
}
