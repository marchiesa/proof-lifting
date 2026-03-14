// Validate BST Property on Array -- Test cases

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] < a[j]
}

method {:axiom} ValidateBST(a: seq<int>) returns (valid: bool)
  ensures valid <==> IsSorted(a)

method TestSorted()
{
  var a := [1, 2, 3, 4, 5];
  var v := ValidateBST(a);
  assert a[0] < a[1] < a[2] < a[3] < a[4];
  assert IsSorted(a);
  assert v;
}

method TestUnsorted()
{
  var a := [1, 3, 2, 4, 5];
  assert a[1] == 3;
  assert a[2] == 2;
  assert !(a[1] < a[2]);
  assert !IsSorted(a);
  var v := ValidateBST(a);
  assert !v;
}

method TestEmpty()
{
  var a: seq<int> := [];
  var v := ValidateBST(a);
  assert v;
}

method TestSingle()
{
  var a := [42];
  var v := ValidateBST(a);
  assert v;
}

method TestDuplicates()
{
  var a := [1, 1, 2];
  assert a[0] == 1 && a[1] == 1;
  assert !(a[0] < a[1]);
  assert !IsSorted(a);
  var v := ValidateBST(a);
  assert !v;
}
