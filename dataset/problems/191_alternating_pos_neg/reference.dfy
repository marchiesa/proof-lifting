// Rearrange Array Alternating Positive/Negative -- Reference solution with invariants

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
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < |pos| ==> pos[j] > 0
    invariant forall j :: 0 <= j < |neg| ==> neg[j] < 0
    invariant multiset(pos) + multiset(neg) == multiset(a[..i])
    decreases |a| - i
  {
    if a[i] > 0 {
      pos := pos + [a[i]];
    } else {
      neg := neg + [a[i]];
    }
    i := i + 1;
  }
  assert a[..i] == a;

  result := [];
  i := 0;
  while i < |pos|
    invariant 0 <= i <= |pos|
    invariant |result| == 2 * i
    invariant Alternating(result)
    invariant |pos| == |neg|
    invariant multiset(result) == multiset(pos[..i]) + multiset(neg[..i])
    decreases |pos| - i
  {
    result := result + [pos[i], neg[i]];
    i := i + 1;
  }
  assert pos[..i] == pos;
  assert neg[..i] == neg;
}
