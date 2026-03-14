// Serialize/Deserialize Binary Tree (as array)
// Task: Add loop invariants so that Dafny can verify this program.
// We use -1 as null marker. Level-order traversal.

// Check if array is a valid serialization: children of node i are at 2i+1 and 2i+2
// Valid means: if parent is null, children must be null too.
predicate ValidSerialization(a: seq<int>, n: int)
  requires 0 <= n <= |a|
{
  forall i :: 0 <= i < n ==>
    (a[i] == -1 ==>
      (2 * i + 1 < n ==> a[2*i+1] == -1) &&
      (2 * i + 2 < n ==> a[2*i+2] == -1))
}

// Count non-null nodes
function CountNodes(a: seq<int>, n: int): int
  requires 0 <= n <= |a|
{
  if n == 0 then 0
  else (if a[n-1] != -1 then 1 else 0) + CountNodes(a, n - 1)
}

method CountTreeNodes(a: seq<int>) returns (count: int)
  requires ValidSerialization(a, |a|)
  ensures count == CountNodes(a, |a|)
{
  count := 0;
  var i := 0;
  while i < |a|
  {
    if a[i] != -1 {
      count := count + 1;
    }
    i := i + 1;
  }
}
