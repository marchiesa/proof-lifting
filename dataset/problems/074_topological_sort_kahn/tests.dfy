// Topological Sort -- Test cases

method {:axiom} KahnTopSort(graph: seq<seq<bool>>, n: int) returns (order: seq<int>, count: int)
  requires n >= 0
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  ensures |order| == count
  ensures 0 <= count <= n
  ensures forall k :: 0 <= k < count ==> 0 <= order[k] < n
  ensures forall i, j :: 0 <= i < j < count ==> order[i] != order[j]

method TestDAG()
{
  // 0 -> 1 -> 2
  var g := [[false, true, false], [false, false, true], [false, false, false]];
  var order, count := KahnTopSort(g, 3);
  assert count <= 3;
}
