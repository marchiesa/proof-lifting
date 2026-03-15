// Decode String (simplified)
// Task: Add loop invariants so that Dafny can verify this program.
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
