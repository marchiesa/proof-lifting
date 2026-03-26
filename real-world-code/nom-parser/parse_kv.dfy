// Parser combinator pattern — abstracted from Rust's nom crate
// (rust-bakery/nom)
//
// nom parsers return (remaining_input, parsed_value) and each step
// receives the remaining slice from the previous step.
// This models parsing "KEY: 123\n" by chaining: match key, skip colon,
// skip spaces, parse digits.

// A parse result: (remaining input, parsed value)
// None means parse failure.
datatype ParseResult<T> = Ok(rest: seq<char>, value: T) | Fail

// --- Primitive combinators (model nom's tag, take_while, etc.) ---

// Match a literal prefix — like nom's tag()
function Tag(input: seq<char>, expected: seq<char>): ParseResult<seq<char>>
  ensures Tag(input, expected).Ok? ==>
    |Tag(input, expected).rest| == |input| - |expected| &&
    Tag(input, expected).rest == input[|expected|..]
{
  if |expected| <= |input| && input[..|expected|] == expected then
    Ok(input[|expected|..], expected)
  else
    Fail
}

// Count how many leading chars satisfy pred
function CountWhile(input: seq<char>, pred: char -> bool, i: nat): (r: nat)
  requires i <= |input|
  ensures i <= r <= |input|
  ensures forall j :: i <= j < r ==> pred(input[j])
  ensures r < |input| ==> !pred(input[r])
  decreases |input| - i
{
  if i < |input| && pred(input[i]) then CountWhile(input, pred, i + 1)
  else i
}

// Consume while predicate holds — like nom's take_while()
function TakeWhile(input: seq<char>, pred: char -> bool): ParseResult<seq<char>>
  ensures TakeWhile(input, pred).Ok?
  ensures |TakeWhile(input, pred).rest| <= |input|
  ensures TakeWhile(input, pred).rest == input[|TakeWhile(input, pred).value|..]
  ensures forall j :: 0 <= j < |TakeWhile(input, pred).value| ==> pred(TakeWhile(input, pred).value[j])
{
  var n := CountWhile(input, pred, 0);
  Ok(input[n..], input[..n])
}

// Consume while predicate holds, require at least 1 — like nom's take_while1()
function TakeWhile1(input: seq<char>, pred: char -> bool): ParseResult<seq<char>>
  ensures TakeWhile1(input, pred).Ok? ==>
    |TakeWhile1(input, pred).value| > 0 &&
    |TakeWhile1(input, pred).rest| < |input| &&
    TakeWhile1(input, pred).rest == input[|TakeWhile1(input, pred).value|..] &&
    forall j :: 0 <= j < |TakeWhile1(input, pred).value| ==> pred(TakeWhile1(input, pred).value[j])
{
  var n := CountWhile(input, pred, 0);
  if n > 0 then Ok(input[n..], input[..n])
  else Fail
}

predicate IsDigit(c: char) { '0' <= c <= '9' }
predicate IsSpace(c: char) { c == ' ' }

// Convert digit characters to a number
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

// --- The composed parser (models a nom parser chain) ---
// Parses "KEY: 123\n" and returns the numeric value.

method ParseKeyValue(input: seq<char>, key: seq<char>) returns (result: ParseResult<nat>)
  requires |key| > 0
  ensures result.Ok? ==>
    |result.rest| < |input| &&
    exists i :: 0 <= i <= |input| && result.rest == input[i..]
{
  // Step 1: match the key
  var step1 := Tag(input, key);
  if step1.Fail? { return Fail; }

  // Step 2: match ":"
  var step2 := Tag(step1.rest, [':']);
  if step2.Fail? { return Fail; }

  // Step 3: skip spaces
  var step3 := TakeWhile(step2.rest, IsSpace);

  // Step 4: parse digits
  var step4 := TakeWhile1(step3.rest, IsDigit);
  if step4.Fail? { return Fail; }

  // Step 5: match newline
  var step5 := Tag(step4.rest, ['\n']);
  if step5.Fail? { return Fail; }

  var value := DigitsToNat(step4.value);
  return Ok(step5.rest, value);
}
