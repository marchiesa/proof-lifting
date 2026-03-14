// Connected Components (iterative label propagation) -- Test cases

method {:axiom} AssignComponents(n: int, adj: seq<seq<int>>) returns (comp: array<int>)
  requires n > 0
  requires |adj| == n
  requires forall i :: 0 <= i < n ==> forall j :: 0 <= j < |adj[i]| ==> 0 <= adj[i][j] < n
  ensures comp.Length == n
  ensures forall i :: 0 <= i < n ==> comp[i] >= 0

method TestSingleNode()
{
  var c := AssignComponents(1, [[]]);
  assert c[0] >= 0;
}

method TestDisconnected()
{
  var c := AssignComponents(3, [[], [], []]);
  assert c[0] >= 0;
  assert c[1] >= 0;
  assert c[2] >= 0;
}

method TestConnected()
{
  var c := AssignComponents(3, [[1], [0, 2], [1]]);
  assert c[0] >= 0;
  assert c[1] >= 0;
  assert c[2] >= 0;
}

method TestTwoComponents()
{
  var c := AssignComponents(4, [[1], [0], [3], [2]]);
  assert c[0] >= 0;
  assert c[2] >= 0;
}
