ghost predicate IsPermutation(p: seq<int>, n: int)
{
  n >= 1 &&
  |p| == n &&
  (forall i | 1 <= i <= n :: exists j | 0 <= j < n :: p[j] == i)
}

ghost predicate IsMerge(a: seq<int>, s1: seq<int>, s2: seq<int>)
  decreases |a|
{
  if |a| == 0 then
    |s1| == 0 && |s2| == 0
  else
    (|s1| > 0 && a[0] == s1[0] && IsMerge(a[1..], s1[1..], s2)) ||
    (|s2| > 0 && a[0] == s2[0] && IsMerge(a[1..], s1, s2[1..]))
}

method RestorePermutation(n: int, a: seq<int>) returns (p: seq<int>)
  requires n >= 1
  requires |a| == 2 * n
  requires forall i | 0 <= i < |a| :: 1 <= a[i] <= n
  ensures IsPermutation(p, n)
  ensures IsMerge(a, p, p)
{
  var seen: set<int> := {};
  p := [];
  for i := 0 to |a| {
    if a[i] !in seen {
      p := p + [a[i]];
      seen := seen + {a[i]};
    }
  }
}