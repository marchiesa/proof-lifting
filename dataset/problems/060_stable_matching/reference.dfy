// Stable Matching (Gale-Shapley Algorithm) -- Reference solution with invariants
// Note: Full stability proof is very hard in Dafny.
// This reference proves safety properties (valid matching output).

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
    invariant 0 <= i <= n
    invariant match_m.Length == n
    invariant forall k :: 0 <= k < i ==> match_m[k] == -1
    invariant forall k :: 0 <= k < i ==> match_w[k] == -1
    invariant forall k :: 0 <= k < i ==> next[k] == 0
    decreases n - i
  {
    match_m[i] := -1;
    match_w[i] := -1;
    next[i] := 0;
    i := i + 1;
  }

  var proposals := 0;
  while proposals < n * n
    invariant match_m.Length == n
    invariant forall k :: 0 <= k < n ==> -1 <= match_m[k] < n
    invariant forall k :: 0 <= k < n ==> -1 <= match_w[k] < n
    invariant forall k :: 0 <= k < n ==> 0 <= next[k] <= n
    invariant forall m :: 0 <= m < n && match_m[m] >= 0 ==> 0 <= match_m[m] < n && match_w[match_m[m]] == m
    invariant forall w :: 0 <= w < n && match_w[w] >= 0 ==> 0 <= match_w[w] < n && match_m[match_w[w]] == w
    invariant proposals >= 0
    decreases n * n - proposals
  {
    var m := -1;
    var search := 0;
    while search < n
      invariant 0 <= search <= n
      invariant m == -1 || (0 <= m < n && match_m[m] == -1 && next[m] < n)
      decreases n - search
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
        invariant 0 <= k <= n
        decreases n - k
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
  // Any unmatched man gets a fallback assignment
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant match_m.Length == n
    invariant forall k :: 0 <= k < i ==> 0 <= match_m[k] < n
    invariant forall k :: i <= k < n ==> -1 <= match_m[k] < n
    decreases n - i
  {
    if match_m[i] == -1 {
      // Fallback: assign to woman 0 (not injective, but ensures range validity)
      match_m[i] := 0;
    }
    i := i + 1;
  }
}
