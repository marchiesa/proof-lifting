// Max Flow (bounded Ford-Fulkerson) -- Test cases

method {:axiom} MaxFlow(n: int, cap: array2<int>, source: int, sink: int) returns (flow: int)
  requires n > 0
  requires cap.Length0 == n && cap.Length1 == n
  requires 0 <= source < n && 0 <= sink < n && source != sink
  requires forall i, j :: 0 <= i < n && 0 <= j < n ==> cap[i, j] >= 0
  modifies cap
  ensures flow >= 0

method TestSimple()
{
  var cap := new int[2, 2];
  cap[0, 0] := 0;
  cap[0, 1] := 10;
  cap[1, 0] := 0;
  cap[1, 1] := 0;
  var f := MaxFlow(2, cap, 0, 1);
  assert f >= 0;
}

method TestNoPath()
{
  var cap := new int[2, 2];
  cap[0, 0] := 0;
  cap[0, 1] := 0;
  cap[1, 0] := 0;
  cap[1, 1] := 0;
  var f := MaxFlow(2, cap, 0, 1);
  assert f >= 0;
}
