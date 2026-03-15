// Majority Element -- Reference solution with invariants

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

lemma CountPrefix(s: seq<int>, v: int, i: int)
  requires 0 <= i < |s|
  ensures Count(s[..i+1], v) == Count(s[..i], v) + (if s[i] == v then 1 else 0)
{
  if i == 0 {
    assert s[..1] == [s[0]];
    assert s[..0] == [];
  } else {
    assert s[..i+1] == [s[0]] + s[1..i+1];
    assert s[..i] == [s[0]] + s[1..i];
    CountPrefix(s[1..], v, i - 1);
    assert s[1..][..i] == s[1..i+1];
    assert s[1..][..i-1] == s[1..i];
  }
}

lemma CountNonNeg(s: seq<int>, v: int)
  ensures Count(s, v) >= 0
  decreases |s|
{
  if |s| > 0 { CountNonNeg(s[1..], v); }
}

lemma CountPositiveImpliesPresent(s: seq<int>, v: int)
  requires Count(s, v) > 0
  ensures exists i :: 0 <= i < |s| && s[i] == v
  decreases |s|
{
  if s[0] == v {
  } else {
    CountPositiveImpliesPresent(s[1..], v);
    var i :| 0 <= i < |s[1..]| && s[1..][i] == v;
    assert s[i+1] == v;
  }
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
    invariant 0 <= i <= |a|
    invariant !found
    invariant forall idx :: 0 <= idx < i ==> !IsMajority(a, a[idx])
    decreases |a| - i
  {
    var c := 0;
    var j := 0;
    while j < |a|
      invariant 0 <= j <= |a|
      invariant c == Count(a[..j], a[i])
      decreases |a| - j
    {
      CountPrefix(a, a[i], j);
      if a[j] == a[i] {
        c := c + 1;
      }
      j := j + 1;
    }
    assert a[..j] == a;
    if 2 * c > |a| {
      candidate := a[i];
      found := true;
      return;
    }
    i := i + 1;
  }

  // If we reach here, no a[i] is a majority. We need to show no v is majority.
  // If some v were majority, Count(a, v) > 0 so v appears in a, contradicting our loop.
  forall v
    ensures !IsMajority(a, v)
  {
    CountNonNeg(a, v);
    if IsMajority(a, v) {
      CountPositiveImpliesPresent(a, v);
      var idx :| 0 <= idx < |a| && a[idx] == v;
      assert !IsMajority(a, a[idx]);
    }
  }
}
