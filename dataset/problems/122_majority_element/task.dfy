// Majority Element
// Task: Add loop invariants so that Dafny can verify this program.
// Find the element that appears more than n/2 times in a sequence.

function Count(s: seq<int>, v: int): int
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == v then 1 else 0) + Count(s[1..], v)
}

predicate IsMajority(s: seq<int>, v: int)
{
  2 * Count(s, v) > |s|
}

method FindMajority(a: seq<int>) returns (found: bool, candidate: int)
  requires |a| > 0
  ensures found ==> IsMajority(a, candidate)
  ensures !found ==> forall v :: !IsMajority(a, v)
{
  found := false;
  candidate := 0;
  var i := 0;
  while i < |a|
  {
    var c := 0;
    var j := 0;
    while j < |a|
    {
      if a[j] == a[i] {
        c := c + 1;
      }
      j := j + 1;
    }
    if 2 * c > |a| {
      candidate := a[i];
      found := true;
      return;
    }
    i := i + 1;
  }
}
