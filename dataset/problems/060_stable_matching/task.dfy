// Stable Matching (Gale-Shapley Algorithm)
// Task: Add loop invariants so that Dafny can verify this program.

// pref_m[i][j] = man i's j-th choice (0-indexed)
// pref_w[i][j] = woman i's j-th choice
// Output: match_m[i] = woman matched to man i

method GaleShapley(n: int, pref_m: seq<seq<int>>, pref_w: seq<seq<int>>) returns (match_m: array<int>)
  requires n > 0
  requires |pref_m| == n
  requires |pref_w| == n
  requires forall i :: 0 <= i < n ==> |pref_m[i]| == n
  requires forall i :: 0 <= i < n ==> |pref_w[i]| == n
  requires forall i, j :: 0 <= i < n && 0 <= j < n ==> 0 <= pref_m[i][j] < n
  requires forall i, j :: 0 <= i < n && 0 <= j < n ==> 0 <= pref_w[i][j] < n
  ensures match_m.Length == n
  ensures forall i :: 0 <= i < n ==> 0 <= match_m[i] < n
{
  match_m := new int[n];
  var match_w := new int[n];
  var next := new int[n];

  var i := 0;
  while i < n
  {
    match_m[i] := -1;
    match_w[i] := -1;
    next[i] := 0;
    i := i + 1;
  }

  var proposals := 0;
  while proposals < n * n
  {
    var m := -1;
    var search := 0;
    while search < n
    {
      if match_m[search] == -1 && next[search] < n {
        m := search;
        break;
      }
      search := search + 1;
    }

    if m == -1 { break; }

    var w := pref_m[m][next[m]];
    next[m] := next[m] + 1;

    if match_w[w] == -1 {
      match_m[m] := w;
      match_w[w] := m;
    } else {
      var m' := match_w[w];
      var prefers_m := false;
      var k := 0;
      while k < n
      {
        if pref_w[w][k] == m { prefers_m := true; break; }
        if pref_w[w][k] == m' { break; }
        k := k + 1;
      }
      if prefers_m {
        match_m[m'] := -1;
        match_m[m] := w;
        match_w[w] := m;
      }
    }
    proposals := proposals + 1;
  }

  // Ensure all men have valid matches
  i := 0;
  while i < n
  {
    if match_m[i] == -1 {
      match_m[i] := 0;
    }
    i := i + 1;
  }
}
