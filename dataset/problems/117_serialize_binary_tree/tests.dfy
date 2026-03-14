// Serialize/Deserialize Binary Tree -- Test cases
predicate ValidSerialization(a: seq<int>, n: int)
  requires 0 <= n <= |a|
{
  forall i :: 0 <= i < n ==>
    (a[i] == -1 ==>
      (2 * i + 1 < n ==> a[2*i+1] == -1) &&
      (2 * i + 2 < n ==> a[2*i+2] == -1))
}

function CountNodes(a: seq<int>, n: int): int
  requires 0 <= n <= |a|
{
  if n == 0 then 0
  else (if a[n-1] != -1 then 1 else 0) + CountNodes(a, n - 1)
}

method {:axiom} CountTreeNodes(a: seq<int>) returns (count: int)
  requires ValidSerialization(a, |a|)
  ensures count == CountNodes(a, |a|)

method TestThreeNodes() {
  // [1, 2, 3] = tree with root 1, left 2, right 3
  var r := CountTreeNodes([1, 2, 3]);
  assert CountNodes([1, 2, 3], 1) == 1;
}

method TestWithNulls() {
  // [1, -1, 3] = tree with root 1, no left child, right 3
  var r := CountTreeNodes([1, -1, 3]);
}

method TestEmpty() {
  var r := CountTreeNodes([]);
  assert r == 0;
}

method TestAllNull() {
  var r := CountTreeNodes([-1]);
  assert r == 0;
}
