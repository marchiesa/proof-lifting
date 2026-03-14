// Stable Matching (Gale-Shapley) -- Test cases

method {:axiom} GaleShapley(n: int, pref_m: seq<seq<int>>, pref_w: seq<seq<int>>) returns (match_m: array<int>)
  requires n > 0
  requires |pref_m| == n
  requires |pref_w| == n
  requires forall i :: 0 <= i < n ==> |pref_m[i]| == n
  requires forall i :: 0 <= i < n ==> |pref_w[i]| == n
  requires forall i, j :: 0 <= i < n && 0 <= j < n ==> 0 <= pref_m[i][j] < n
  requires forall i, j :: 0 <= i < n && 0 <= j < n ==> 0 <= pref_w[i][j] < n
  ensures match_m.Length == n
  ensures forall i :: 0 <= i < n ==> 0 <= match_m[i] < n

method TestSingle()
{
  var m := GaleShapley(1, [[0]], [[0]]);
  assert m[0] == 0;
}

method TestTwo()
{
  var m := GaleShapley(2, [[0, 1], [1, 0]], [[0, 1], [1, 0]]);
  assert 0 <= m[0] < 2;
  assert 0 <= m[1] < 2;
}

method TestThree()
{
  var m := GaleShapley(3,
    [[0, 1, 2], [1, 0, 2], [2, 1, 0]],
    [[0, 1, 2], [1, 0, 2], [2, 1, 0]]);
  assert 0 <= m[0] < 3;
  assert 0 <= m[1] < 3;
  assert 0 <= m[2] < 3;
}
