// Plus One: Increment number represented as digit array
// Task: Add loop invariants so that Dafny can verify this program.

predicate ValidDigits(digits: seq<int>)
{
  forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
}

// Recursive specification of "add 1 with carry from the right"
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
  {
    result := result[..i] + [0] + result[i+1..];
    i := i - 1;
  }
  if i < 0 {
    result := [1] + result;
  } else {
    result := result[..i] + [result[i] + 1] + result[i+1..];
  }
}
