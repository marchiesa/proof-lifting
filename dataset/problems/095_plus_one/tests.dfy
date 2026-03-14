// Plus One -- Test cases

predicate ValidDigits(digits: seq<int>)
{
  forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
}

function PlusOneSpec(digits: seq<int>): seq<int>
  requires ValidDigits(digits)
  decreases |digits|
{
  if |digits| == 0 then [1]
  else if digits[|digits|-1] < 9 then
    digits[..|digits|-1] + [digits[|digits|-1] + 1]
  else
    PlusOneSpec(digits[..|digits|-1]) + [0]
}

method {:axiom} PlusOne(digits: seq<int>) returns (result: seq<int>)
  requires |digits| > 0
  requires ValidDigits(digits)
  ensures result == PlusOneSpec(digits)
  ensures ValidDigits(result)

method TestNoCarry()
{
  var d := [1, 2, 3];
  var r := PlusOne(d);
  assert r == PlusOneSpec(d);
  assert PlusOneSpec(d) == [1, 2, 4];
  assert r == [1, 2, 4];
}

method TestWithCarry()
{
  var d := [1, 2, 9];
  var r := PlusOne(d);
  assert PlusOneSpec(d) == PlusOneSpec([1, 2]) + [0];
  assert PlusOneSpec([1, 2]) == [1, 3];
  assert r == [1, 3, 0];
}

method TestAllNines()
{
  var d := [9, 9, 9];
  var r := PlusOne(d);
  assert |r| == 4;
}

method TestSingle()
{
  var d := [0];
  var r := PlusOne(d);
  assert r == [1];
}
