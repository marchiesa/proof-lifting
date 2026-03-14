// Maximum Bipartite Matching (Hungarian-style augmenting paths)
// Task: Add loop invariants so that Dafny can verify this program.

method MaxMatching(graph: seq<seq<bool>>, nLeft: int, nRight: int) returns (matchCount: nat)
  requires nLeft >= 0 && nRight >= 0
  requires |graph| == nLeft
  requires forall i :: 0 <= i < nLeft ==> |graph[i]| == nRight
  ensures matchCount <= nLeft
  ensures matchCount <= nRight
{
  var matchRight := seq(nRight, _ => -1);
  matchCount := 0;
  var u := 0;
  while u < nLeft
  {
    var visited := seq(nRight, _ => false);
    var found := false;
    var newMR := matchRight;
    found, newMR := TryAugment(graph, nLeft, nRight, u, newMR, visited, nRight);
    if found {
      matchRight := newMR;
      if matchCount < nRight {
        matchCount := matchCount + 1;
      }
    }
    u := u + 1;
  }
}

method TryAugment(graph: seq<seq<bool>>, nLeft: int, nRight: int, u: int,
                   matchRight: seq<int>, visited: seq<bool>, fuel: nat)
    returns (found: bool, newMR: seq<int>)
  requires nLeft >= 0 && nRight >= 0
  requires |graph| == nLeft
  requires forall i :: 0 <= i < nLeft ==> |graph[i]| == nRight
  requires 0 <= u < nLeft
  requires |matchRight| == nRight
  requires |visited| == nRight
  requires forall j :: 0 <= j < nRight ==> matchRight[j] >= -1
  requires forall j :: 0 <= j < nRight && matchRight[j] >= 0 ==> matchRight[j] < nLeft
  ensures |newMR| == nRight
  ensures forall j :: 0 <= j < nRight ==> newMR[j] >= -1
  ensures forall j :: 0 <= j < nRight && newMR[j] >= 0 ==> newMR[j] < nLeft
  decreases fuel
{
  newMR := matchRight;
  found := false;
  if fuel == 0 { return; }
  var v := 0;
  var vis := visited;
  var mr := matchRight;
  while v < nRight
  {
    if graph[u][v] && !vis[v] {
      vis := vis[v := true];
      if mr[v] == -1 {
        mr := mr[v := u];
        return true, mr;
      } else {
        var subFound: bool;
        var subMR: seq<int>;
        subFound, subMR := TryAugment(graph, nLeft, nRight, mr[v], mr, vis, fuel - 1);
        if subFound {
          subMR := subMR[v := u];
          return true, subMR;
        }
      }
    }
    v := v + 1;
  }
  return false, mr;
}
