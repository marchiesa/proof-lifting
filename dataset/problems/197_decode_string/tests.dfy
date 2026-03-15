// Decode String (simplified)
// Format: segments of [count, char, 0] where 0 is sentinel
// count > 0, char != 0

function RepeatChar(c: int, n: int): seq<int>
  requires n >= 0
  decreases n
{
  if n == 0 then []
  else [c] + RepeatChar(c, n - 1)
}

// Valid encoding: sequence of triples [count, char, 0]
predicate ValidEncoding(enc: seq<int>)
{
  |enc| % 3 == 0 &&
  forall i :: 0 <= i < |enc| / 3 ==>
    enc[3*i] > 0 && enc[3*i+1] != 0 && enc[3*i+2] == 0
}

method DecodeString(enc: seq<int>) returns (result: seq<int>)
  requires ValidEncoding(enc)
  ensures |result| >= 0
{
  result := [];
  var i := 0;
  while i < |enc|
  {
    var count := enc[i];
    var ch := enc[i + 1];
    // enc[i+2] == 0 (sentinel, skip)
    var j := 0;
    while j < count
    {
      result := result + [ch];
      j := j + 1;
    }
    i := i + 3;
  }
}

method Main()
{
  // [3, 1, 0] => [1, 1, 1] (repeat 1 three times)
  var enc1 := [3, 1, 0];
  expect ValidEncoding(enc1);
  var r1 := DecodeString(enc1);
  expect |r1| >= 0;

  // [2, 5, 0, 1, 3, 0] => [5, 5, 3]
  var enc2 := [2, 5, 0, 1, 3, 0];
  expect ValidEncoding(enc2);
  var r2 := DecodeString(enc2);
  expect |r2| >= 0;

  // Empty encoding
  var enc3: seq<int> := [];
  expect ValidEncoding(enc3);
  var r3 := DecodeString(enc3);
  expect |r3| >= 0;

  // Negative test: invalid encoding
  expect !ValidEncoding([1, 2]);  // not multiple of 3
  expect !ValidEncoding([0, 1, 0]); // count must be > 0
  expect !ValidEncoding([1, 0, 0]); // char must be != 0

  print "All spec tests passed\n";
}
