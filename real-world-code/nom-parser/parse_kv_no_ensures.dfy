// Same parser, but without ensures on the combinators.
// Can Dafny still verify the postcondition?

datatype ParseResult<T> = Ok(rest: seq<char>, value: T) | Fail

function Tag(input: seq<char>, expected: seq<char>): ParseResult<seq<char>>
{
  if |expected| <= |input| && input[..|expected|] == expected then
    Ok(input[|expected|..], expected)
  else
    Fail
}

function CountWhile(input: seq<char>, pred: char -> bool, i: nat): (r: nat)
  requires i <= |input|
  decreases |input| - i
{
  if i < |input| && pred(input[i]) then CountWhile(input, pred, i + 1)
  else i
}

function TakeWhile(input: seq<char>, pred: char -> bool): ParseResult<seq<char>>
{
  var n := CountWhile(input, pred, 0);
  Ok(input[n..], input[..n])
}

function TakeWhile1(input: seq<char>, pred: char -> bool): ParseResult<seq<char>>
{
  var n := CountWhile(input, pred, 0);
  if n > 0 then Ok(input[n..], input[..n])
  else Fail
}

predicate IsDigit(c: char) { '0' <= c <= '9' }
predicate IsSpace(c: char) { c == ' ' }

function CharToDigit(c: char): nat
  requires IsDigit(c)
{
  (c - '0') as nat
}

function DigitsToNat(digits: seq<char>): nat
  requires |digits| > 0
  requires forall i :: 0 <= i < |digits| ==> IsDigit(digits[i])
{
  if |digits| == 1 then CharToDigit(digits[0])
  else DigitsToNat(digits[..|digits|-1]) * 10 + CharToDigit(digits[|digits|-1])
}

method ParseKeyValue(input: seq<char>, key: seq<char>) returns (result: ParseResult<nat>)
  requires |key| > 0
  ensures result.Ok? ==>
    |result.rest| < |input| &&
    exists i :: 0 <= i <= |input| && result.rest == input[i..]
{
  var step1 := Tag(input, key);
  if step1.Fail? { return Fail; }

  var step2 := Tag(step1.rest, [':']);
  if step2.Fail? { return Fail; }

  var step3 := TakeWhile(step2.rest, IsSpace);

  var step4 := TakeWhile1(step3.rest, IsDigit);
  if step4.Fail? { return Fail; }

  var step5 := Tag(step4.rest, ['\n']);
  if step5.Fail? { return Fail; }

  var value := DigitsToNat(step4.value);
  return Ok(step5.rest, value);
}
