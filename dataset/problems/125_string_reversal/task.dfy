// String Reversal
// Task: Add loop invariants so that Dafny can verify this program.
// Reverse a sequence of characters.

function Reverse(s: seq<char>): seq<char>
  decreases |s|
{
  if |s| == 0 then []
  else Reverse(s[1..]) + [s[0]]
}

predicate IsReverse(s: seq<char>, r: seq<char>)
{
  |r| == |s| && forall i :: 0 <= i < |s| ==> r[i] == s[|s| - 1 - i]
}

method ReverseSeq(s: seq<char>) returns (r: seq<char>)
  ensures IsReverse(s, r)
{
  r := [];
  var i := 0;
  while i < |s|
  {
    r := [s[i]] + r;
    i := i + 1;
  }
}
