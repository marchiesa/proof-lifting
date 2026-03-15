// Decode String -- Reference solution with invariants

function RepeatChar(c: int, n: int): seq<int>
  requires n >= 0
  decreases n
{
  if n == 0 then []
  else [c] + RepeatChar(c, n - 1)
}

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
    invariant 0 <= i <= |enc|
    invariant i % 3 == 0
    decreases |enc| - i
  {
    var count := enc[i];
    var ch := enc[i + 1];
    var j := 0;
    while j < count
      invariant 0 <= j <= count
      decreases count - j
    {
      result := result + [ch];
      j := j + 1;
    }
    i := i + 3;
  }
}
