// Reverse a Linked List (Sequence-Based)

predicate IsReverse(a: seq<int>, b: seq<int>)
{
  |a| == |b| && forall i :: 0 <= i < |a| ==> a[i] == b[|b| - 1 - i]
}

method ReverseList(a: seq<int>) returns (result: seq<int>)
  ensures IsReverse(a, result)
  ensures |result| == |a|
{
  result := [];
  var i := 0;
  while i < |a|
  {
    result := [a[i]] + result;
    i := i + 1;
  }
}

method Main()
{
  var a := [1, 2, 3, 4, 5];
  var r := ReverseList(a);
  expect |r| == 5;
  expect IsReverse(a, r);
  expect r[0] == 5;
  expect r[4] == 1;

  // Empty sequence
  var e: seq<int> := [];
  var re := ReverseList(e);
  expect |re| == 0;
  expect IsReverse(e, re);

  // Single element
  var s := [42];
  var rs := ReverseList(s);
  expect |rs| == 1;
  expect rs[0] == 42;
  expect IsReverse(s, rs);

  // Palindrome stays the same
  var p := [1, 2, 1];
  var rp := ReverseList(p);
  expect IsReverse(p, rp);
  expect rp[0] == 1 && rp[1] == 2 && rp[2] == 1;

  // Negative test: non-reverse should fail
  var nr := [1, 2, 3];
  expect !IsReverse(nr, [1, 2, 3]);
  expect IsReverse(nr, [3, 2, 1]);

  print "All spec tests passed\n";
}
