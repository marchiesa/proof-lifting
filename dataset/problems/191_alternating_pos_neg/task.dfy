// Rearrange Array Alternating Positive/Negative
// Task: Add loop invariants so that Dafny can verify this program.

predicate NoZeros(a: seq<int>)
{
  forall i :: 0 <= i < |a| ==> a[i] != 0
}

predicate Alternating(a: seq<int>)
{
  forall i :: 0 <= i < |a| ==>
    (i % 2 == 0 ==> a[i] > 0) && (i % 2 == 1 ==> a[i] < 0)
}

function CountPos(a: seq<int>): nat
{
  if |a| == 0 then 0
  else (if a[0] > 0 then 1 else 0) + CountPos(a[1..])
}

function CountNeg(a: seq<int>): nat
{
  if |a| == 0 then 0
  else (if a[0] < 0 then 1 else 0) + CountNeg(a[1..])
}

method Rearrange(a: seq<int>) returns (result: seq<int>)
  requires NoZeros(a)
  requires |a| % 2 == 0
  requires CountPos(a) == CountNeg(a)
  ensures |result| == |a|
  ensures Alternating(result)
  ensures multiset(result) == multiset(a)
{
  var pos: seq<int> := [];
  var neg: seq<int> := [];
  var i := 0;
  while i < |a|
  {
    if a[i] > 0 {
      pos := pos + [a[i]];
    } else {
      neg := neg + [a[i]];
    }
    i := i + 1;
  }

  result := [];
  i := 0;
  while i < |pos|
  {
    result := result + [pos[i], neg[i]];
    i := i + 1;
  }
}
