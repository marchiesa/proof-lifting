// Count Distinct Subsequences -- Test cases
function NumDistinct(s: seq<int>, t: seq<int>, si: int, ti: int): nat
  requires 0 <= si <= |s|
  requires 0 <= ti <= |t|
  decreases |s| - si, |t| - ti
{
  if ti == |t| then 1
  else if si == |s| then 0
  else
    (if s[si] == t[ti] then NumDistinct(s, t, si + 1, ti + 1) else 0) +
    NumDistinct(s, t, si + 1, ti)
}

method {:axiom} CountDistinctSubsequences(s: seq<int>, t: seq<int>) returns (result: nat)
  ensures result == NumDistinct(s, t, 0, 0)

method TestBasic() {
  // s = [1,2,1], t = [1,1] -> subsequences: (pos 0, pos 2) -> 1
  var r := CountDistinctSubsequences([1, 2, 1], [1, 1]);
}

method TestNoMatch() {
  var r := CountDistinctSubsequences([1, 2], [3]);
  assert NumDistinct([1, 2], [3], 0, 0) == 0;
  assert r == 0;
}

method TestEmptyTarget() {
  var r := CountDistinctSubsequences([1, 2, 3], []);
  assert r == 1;
}
