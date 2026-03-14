// Segment Tree -- Reference solution with invariants

function SumRange(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0 else a[lo] + SumRange(a, lo + 1, hi)
}

method BuildTree(a: seq<int>) returns (tree: array<int>, n: int)
  requires |a| > 0
  ensures n == |a|
  ensures tree.Length == 4 * n
{
  n := |a|;
  tree := new int[4 * n](_ => 0);
  BuildHelper(tree, a, 1, 0, n - 1);
}

method BuildHelper(tree: array<int>, a: seq<int>, node: int, lo: int, hi: int)
  requires tree.Length >= 1
  requires 0 <= lo <= hi < |a|
  requires 1 <= node
  requires node < tree.Length
  requires 2 * node < tree.Length
  requires 2 * node + 1 < tree.Length
  modifies tree
  decreases hi - lo
{
  if lo == hi {
    tree[node] := a[lo];
  } else {
    var mid := lo + (hi - lo) / 2;
    if 2 * (2 * node) + 1 < tree.Length && 2 * (2 * node + 1) + 1 < tree.Length {
      BuildHelper(tree, a, 2 * node, lo, mid);
      BuildHelper(tree, a, 2 * node + 1, mid + 1, hi);
      tree[node] := tree[2 * node] + tree[2 * node + 1];
    }
  }
}

method Update(tree: array<int>, node: int, lo: int, hi: int, idx: int, val: int)
  requires 0 <= lo <= hi
  requires 1 <= node
  requires node < tree.Length
  requires 2 * node < tree.Length
  requires 2 * node + 1 < tree.Length
  requires lo <= idx <= hi
  modifies tree
  decreases hi - lo
{
  if lo == hi {
    tree[node] := val;
  } else {
    var mid := lo + (hi - lo) / 2;
    if 2 * (2 * node) + 1 < tree.Length && 2 * (2 * node + 1) + 1 < tree.Length {
      if idx <= mid {
        Update(tree, 2 * node, lo, mid, idx, val);
      } else {
        Update(tree, 2 * node + 1, mid + 1, hi, idx, val);
      }
      tree[node] := tree[2 * node] + tree[2 * node + 1];
    }
  }
}

method Query(tree: array<int>, node: int, lo: int, hi: int, qlo: int, qhi: int) returns (sum: int)
  requires 0 <= lo <= hi
  requires 1 <= node
  requires node < tree.Length
  requires 2 * node < tree.Length
  requires 2 * node + 1 < tree.Length
  decreases hi - lo
{
  if qlo > hi || qhi < lo {
    return 0;
  }
  if qlo <= lo && hi <= qhi {
    return tree[node];
  }
  var mid := lo + (hi - lo) / 2;
  if 2 * (2 * node) + 1 < tree.Length && 2 * (2 * node + 1) + 1 < tree.Length {
    var leftSum := Query(tree, 2 * node, lo, mid, qlo, qhi);
    var rightSum := Query(tree, 2 * node + 1, mid + 1, hi, qlo, qhi);
    return leftSum + rightSum;
  }
  return 0;
}
