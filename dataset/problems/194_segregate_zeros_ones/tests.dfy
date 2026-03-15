// Segregate 0s and 1s

predicate IsBinary(a: seq<int>)
{
  forall i :: 0 <= i < |a| ==> a[i] == 0 || a[i] == 1
}

predicate IsSegregated(a: seq<int>)
  requires IsBinary(a)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

function CountVal(a: seq<int>, v: int): nat
{
  if |a| == 0 then 0
  else (if a[0] == v then 1 else 0) + CountVal(a[1..], v)
}

method Segregate(a: seq<int>) returns (result: seq<int>)
  requires IsBinary(a)
  ensures IsBinary(result)
  ensures IsSegregated(result)
  ensures |result| == |a|
  ensures multiset(result) == multiset(a)
{
  var zeros := 0;
  var i := 0;
  while i < |a|
  {
    if a[i] == 0 {
      zeros := zeros + 1;
    }
    i := i + 1;
  }
  result := seq(zeros, _ => 0) + seq(|a| - zeros, _ => 1);
}

method Main()
{
  var a := [0, 1, 0, 1, 1, 0];
  var r := Segregate(a);
  expect |r| == 6;
  expect IsBinary(r);
  expect IsSegregated(r);
  expect multiset(r) == multiset(a);

  // All zeros
  var b := [0, 0, 0];
  var rb := Segregate(b);
  expect IsSegregated(rb);
  expect rb == [0, 0, 0];

  // All ones
  var c := [1, 1, 1];
  var rc := Segregate(c);
  expect IsSegregated(rc);

  // Empty
  var d: seq<int> := [];
  var rd := Segregate(d);
  expect |rd| == 0;

  // Already segregated
  var e := [0, 0, 1, 1];
  var re := Segregate(e);
  expect IsSegregated(re);

  // Negative test
  var f := [1, 0];
  expect !IsSegregated(f);

  print "All spec tests passed\n";
}
