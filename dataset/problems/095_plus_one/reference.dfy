// Plus One: Increment number represented as digit array -- Reference solution

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

lemma PlusOneSpecValid(digits: seq<int>)
  requires ValidDigits(digits)
  ensures ValidDigits(PlusOneSpec(digits))
  decreases |digits|
{
  if |digits| > 0 && digits[|digits|-1] >= 9 {
    assert ValidDigits(digits[..|digits|-1]);
    PlusOneSpecValid(digits[..|digits|-1]);
  }
}

lemma PlusOneUnroll(digits: seq<int>, i: int)
  requires ValidDigits(digits)
  requires 0 <= i < |digits|
  requires forall j :: i < j < |digits| ==> digits[j] == 9
  requires digits[i] < 9
  ensures PlusOneSpec(digits) == digits[..i] + [digits[i] + 1] + seq(|digits| - i - 1, k requires 0 <= k => 0)
  decreases |digits| - i
{
  if i == |digits| - 1 {
    assert PlusOneSpec(digits) == digits[..|digits|-1] + [digits[|digits|-1] + 1];
    assert digits[..i] == digits[..|digits|-1];
    assert seq(0, k requires 0 <= k => 0) == [];
  } else {
    assert digits[|digits|-1] == 9;
    assert PlusOneSpec(digits) == PlusOneSpec(digits[..|digits|-1]) + [0];
    var shorter := digits[..|digits|-1];
    assert ValidDigits(shorter);
    assert forall j :: i < j < |shorter| ==> shorter[j] == 9;
    assert shorter[i] < 9;
    PlusOneUnroll(shorter, i);
    assert PlusOneSpec(shorter) == shorter[..i] + [shorter[i] + 1] + seq(|shorter| - i - 1, k requires 0 <= k => 0);
    assert shorter[..i] == digits[..i];
    assert shorter[i] == digits[i];
    // PlusOneSpec(digits) = (digits[..i] + [digits[i]+1] + seq(|shorter|-i-1, _=>0)) + [0]
    //                     = digits[..i] + [digits[i]+1] + seq(|digits|-i-1, _=>0)
    var z1 := seq(|shorter| - i - 1, k requires 0 <= k => 0);
    var z2 := seq(|digits| - i - 1, k requires 0 <= k => 0);
    assert z2 == z1 + [0];
  }
}

lemma PlusOneAllNines(digits: seq<int>)
  requires ValidDigits(digits)
  requires forall j :: 0 <= j < |digits| ==> digits[j] == 9
  ensures PlusOneSpec(digits) == [1] + seq(|digits|, k requires 0 <= k => 0)
  decreases |digits|
{
  if |digits| == 0 {
  } else {
    var shorter := digits[..|digits|-1];
    assert ValidDigits(shorter);
    assert forall j :: 0 <= j < |shorter| ==> shorter[j] == 9;
    PlusOneAllNines(shorter);
    assert PlusOneSpec(digits) == PlusOneSpec(shorter) + [0];
    assert PlusOneSpec(shorter) == [1] + seq(|shorter|, k requires 0 <= k => 0);
    var z1 := seq(|shorter|, k requires 0 <= k => 0);
    var z2 := seq(|digits|, k requires 0 <= k => 0);
    assert z2 == z1 + [0];
  }
}

method PlusOne(digits: seq<int>) returns (result: seq<int>)
  requires |digits| > 0
  requires ValidDigits(digits)
  ensures result == PlusOneSpec(digits)
  ensures ValidDigits(result)
{
  PlusOneSpecValid(digits);
  result := digits;
  var i := |result| - 1;
  while i >= 0 && result[i] == 9
    invariant -1 <= i < |result|
    invariant |result| == |digits|
    invariant result[..i+1] == digits[..i+1]
    invariant forall j :: i + 1 <= j < |result| ==> result[j] == 0
    invariant forall j :: i + 1 <= j < |digits| ==> digits[j] == 9
    invariant ValidDigits(result)
    decreases i + 1
  {
    result := result[..i] + [0] + result[i+1..];
    assert result[..i] == digits[..i];
    i := i - 1;
  }
  if i < 0 {
    assert forall j :: 0 <= j < |digits| ==> digits[j] == 9;
    PlusOneAllNines(digits);
    assert forall j :: 0 <= j < |result| ==> result[j] == 0;
    result := [1] + result;
    assert result == [1] + seq(|digits|, k requires 0 <= k => 0);
  } else {
    assert digits[i] < 9;
    assert forall j :: i < j < |digits| ==> digits[j] == 9;
    PlusOneUnroll(digits, i);
    result := result[..i] + [result[i] + 1] + result[i+1..];
    assert result == digits[..i] + [digits[i] + 1] + seq(|digits| - i - 1, k requires 0 <= k => 0);
  }
}
