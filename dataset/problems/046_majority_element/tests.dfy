// Majority Element -- Test cases

function Count(a: seq<int>, val: int): nat
{
  if |a| == 0 then 0
  else (if a[0] == val then 1 else 0) + Count(a[1..], val)
}

predicate IsMajority(a: seq<int>, val: int)
{
  2 * Count(a, val) > |a|
}

method {:axiom} FindMajority(a: seq<int>) returns (candidate: int)
  requires |a| > 0
  requires exists v :: IsMajority(a, v)
  ensures candidate in a

method TestClear()
{
  var a := [3, 3, 3, 2, 1];
  // Prove 3 is a majority: Count([3,3,3,2,1], 3) = 3, and 2*3 > 5
  assert a[0] == 3;
  assert a[1..] == [3, 3, 2, 1];
  assert a[1..][0] == 3;
  assert a[1..][1..] == [3, 2, 1];
  assert a[1..][1..][0] == 3;
  assert a[1..][1..][1..] == [2, 1];
  assert Count([2, 1], 3) == Count([1], 3);
  assert Count([1], 3) == Count([], 3);
  assert Count([], 3) == 0;
  assert Count(a, 3) == 3;
  assert IsMajority(a, 3);
  var c := FindMajority(a);
  assert c in a;
}

method TestMinimal()
{
  var a := [1];
  assert a[0] == 1;
  assert a[1..] == [];
  assert Count(a, 1) == 1;
  assert IsMajority(a, 1);
  var c := FindMajority(a);
  assert c in a;
}
