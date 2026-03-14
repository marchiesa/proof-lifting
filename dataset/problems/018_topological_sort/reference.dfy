// Topological Sort Existence (Cycle Detection via In-Degree)
// Reference solution with invariants

// Compute in-degree of each node
method ComputeInDegrees(graph: seq<seq<bool>>, n: int) returns (indeg: seq<int>)
  requires n >= 0
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  ensures |indeg| == n
  ensures forall k :: 0 <= k < n ==> indeg[k] >= 0
{
  indeg := seq(n, _ => 0);
  var j := 0;
  while j < n
    invariant 0 <= j <= n
    invariant |indeg| == n
    invariant forall k :: 0 <= k < n ==> indeg[k] >= 0
    decreases n - j
  {
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant |indeg| == n
      invariant forall k :: 0 <= k < n ==> indeg[k] >= 0
      decreases n - i
    {
      if graph[i][j] {
        indeg := indeg[j := indeg[j] + 1];
      }
      i := i + 1;
    }
    j := j + 1;
  }
}

// Number of true values in a boolean sequence
function CountTrue(s: seq<bool>): int
{
  if |s| == 0 then 0
  else (if s[0] then 1 else 0) + CountTrue(s[1..])
}

lemma CountTrueBound(s: seq<bool>)
  ensures 0 <= CountTrue(s) <= |s|
{
  if |s| > 0 {
    CountTrueBound(s[1..]);
  }
}

lemma CountTrueAllFalse(s: seq<bool>)
  requires forall i :: 0 <= i < |s| ==> !s[i]
  ensures CountTrue(s) == 0
{
  if |s| > 0 {
    assert !s[0];
    assert s[1..] == s[1..];
    forall j | 0 <= j < |s[1..]|
      ensures !s[1..][j]
    {
      assert s[1..][j] == s[j + 1];
    }
    CountTrueAllFalse(s[1..]);
  }
}

lemma CountTrueUpdate(s: seq<bool>, i: int)
  requires 0 <= i < |s|
  requires !s[i]
  ensures CountTrue(s[i := true]) == CountTrue(s) + 1
{
  if i == 0 {
    assert s[i := true][1..] == s[1..];
  } else {
    assert s[i := true][1..] == s[1..][i-1 := true];
    CountTrueUpdate(s[1..], i - 1);
  }
}

// Count nodes with zero in-degree in a given indeg array
// Returns the count of processed (zero in-degree) nodes after iterative removal
method CountProcessable(graph: seq<seq<bool>>, n: int) returns (count: int)
  requires n >= 0
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  ensures 0 <= count <= n
{
  var indeg := ComputeInDegrees(graph, n);
  var processed := seq(n, _ => false);
  count := 0;

  CountTrueAllFalse(processed);

  var rounds := n;
  while rounds > 0
    invariant 0 <= rounds <= n
    invariant 0 <= count <= n
    invariant |indeg| == n
    invariant |processed| == n
    invariant count == CountTrue(processed)
    decreases rounds
  {
    var i := 0;
    var foundAny := false;
    while i < n
      invariant 0 <= i <= n
      invariant 0 <= count <= n
      invariant |indeg| == n
      invariant |processed| == n
      invariant count == CountTrue(processed)
      decreases n - i
    {
      if !processed[i] && indeg[i] == 0 {
        CountTrueBound(processed);
        CountTrueUpdate(processed, i);
        processed := processed[i := true];
        count := count + 1;
        CountTrueBound(processed);
        foundAny := true;
        // Reduce in-degrees of neighbors
        var j := 0;
        while j < n
          invariant 0 <= j <= n
          invariant |indeg| == n
          invariant |processed| == n
          invariant count == CountTrue(processed)
          decreases n - j
        {
          if graph[i][j] {
            indeg := indeg[j := indeg[j] - 1];
          }
          j := j + 1;
        }
      }
      i := i + 1;
    }
    if !foundAny {
      rounds := 0;
    } else {
      rounds := rounds - 1;
    }
  }
  CountTrueBound(processed);
}
