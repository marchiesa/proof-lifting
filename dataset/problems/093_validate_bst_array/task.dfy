// Validate BST Property on Array
// Task: Add loop invariants so that Dafny can verify this program.

// Check that an array satisfies the BST property:
// For a complete binary tree stored in an array (1-indexed mapped to 0-indexed),
// we simplify to checking that the array is strictly sorted (in-order traversal
// of a valid BST yields a sorted sequence).

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] < a[j]
}

method ValidateBST(a: seq<int>) returns (valid: bool)
  ensures valid <==> IsSorted(a)
{
  if |a| <= 1 {
    return true;
  }
  var i := 0;
  while i < |a| - 1
  {
    if a[i] >= a[i + 1] {
      return false;
    }
    i := i + 1;
  }
  return true;
}
