// Minimum Vertex Cover on Bipartite Graph -- Reference solution with invariants

method MinVertexCover(graph: seq<seq<bool>>, nLeft: int, nRight: int) returns (coverSize: nat, coverLeft: seq<bool>, coverRight: seq<bool>)
  requires nLeft >= 0 && nRight >= 0
  requires |graph| == nLeft
  requires forall i :: 0 <= i < nLeft ==> |graph[i]| == nRight
  ensures |coverLeft| == nLeft
  ensures |coverRight| == nRight
  ensures coverSize <= nLeft + nRight
{
  var matchLeft := seq(nLeft, _ => -1);
  var matchRight := seq(nRight, _ => -1);
  var matchCount := 0;
  var u := 0;
  while u < nLeft
    invariant 0 <= u <= nLeft
    invariant matchCount <= u
    invariant |matchLeft| == nLeft && |matchRight| == nRight
    invariant forall j :: 0 <= j < nRight ==> matchRight[j] >= -1
    invariant forall j :: 0 <= j < nRight && matchRight[j] >= 0 ==> matchRight[j] < nLeft
    invariant forall i :: 0 <= i < nLeft ==> matchLeft[i] >= -1
    invariant forall i :: 0 <= i < nLeft && matchLeft[i] >= 0 ==> matchLeft[i] < nRight
    decreases nLeft - u
  {
    var visited := seq(nRight, _ => false);
    var found: bool;
    var ml: seq<int>;
    var mr: seq<int>;
    found, ml, mr := Augment(graph, nLeft, nRight, u, matchLeft, matchRight, visited, nRight);
    if found {
      matchLeft := ml;
      matchRight := mr;
      matchCount := matchCount + 1;
    }
    u := u + 1;
  }
  coverLeft := seq(nLeft, _ => false);
  coverRight := seq(nRight, _ => false);
  coverSize := 0;
  var i := 0;
  while i < nLeft
    invariant 0 <= i <= nLeft
    invariant |coverLeft| == nLeft && |coverRight| == nRight
    invariant coverSize <= i
    decreases nLeft - i
  {
    if matchLeft[i] >= 0 {
      coverLeft := coverLeft[i := true];
      coverSize := coverSize + 1;
    }
    i := i + 1;
  }
}

method Augment(graph: seq<seq<bool>>, nLeft: int, nRight: int, u: int,
               matchLeft: seq<int>, matchRight: seq<int>, visited: seq<bool>, fuel: nat)
    returns (found: bool, newML: seq<int>, newMR: seq<int>)
  requires nLeft >= 0 && nRight >= 0
  requires |graph| == nLeft
  requires forall i :: 0 <= i < nLeft ==> |graph[i]| == nRight
  requires 0 <= u < nLeft
  requires |matchLeft| == nLeft && |matchRight| == nRight && |visited| == nRight
  requires forall j :: 0 <= j < nRight ==> matchRight[j] >= -1
  requires forall j :: 0 <= j < nRight && matchRight[j] >= 0 ==> matchRight[j] < nLeft
  requires forall i :: 0 <= i < nLeft ==> matchLeft[i] >= -1
  requires forall i :: 0 <= i < nLeft && matchLeft[i] >= 0 ==> matchLeft[i] < nRight
  ensures |newML| == nLeft && |newMR| == nRight
  ensures forall j :: 0 <= j < nRight ==> newMR[j] >= -1
  ensures forall j :: 0 <= j < nRight && newMR[j] >= 0 ==> newMR[j] < nLeft
  ensures forall i :: 0 <= i < nLeft ==> newML[i] >= -1
  ensures forall i :: 0 <= i < nLeft && newML[i] >= 0 ==> newML[i] < nRight
  decreases fuel
{
  newML := matchLeft;
  newMR := matchRight;
  found := false;
  if fuel == 0 { return; }
  var v := 0;
  var vis := visited;
  var ml := matchLeft;
  var mr := matchRight;
  while v < nRight
    invariant 0 <= v <= nRight
    invariant |vis| == nRight && |ml| == nLeft && |mr| == nRight
    invariant forall j :: 0 <= j < nRight ==> mr[j] >= -1
    invariant forall j :: 0 <= j < nRight && mr[j] >= 0 ==> mr[j] < nLeft
    invariant forall i :: 0 <= i < nLeft ==> ml[i] >= -1
    invariant forall i :: 0 <= i < nLeft && ml[i] >= 0 ==> ml[i] < nRight
    decreases nRight - v
  {
    if graph[u][v] && !vis[v] {
      vis := vis[v := true];
      if mr[v] == -1 {
        ml := ml[u := v];
        mr := mr[v := u];
        return true, ml, mr;
      } else {
        var subFound: bool;
        var subML: seq<int>;
        var subMR: seq<int>;
        subFound, subML, subMR := Augment(graph, nLeft, nRight, mr[v], ml, mr, vis, fuel - 1);
        if subFound {
          subML := subML[u := v];
          subMR := subMR[v := u];
          return true, subML, subMR;
        }
      }
    }
    v := v + 1;
  }
  return false, ml, mr;
}
