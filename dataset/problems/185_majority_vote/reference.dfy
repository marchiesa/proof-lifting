// Majority Element -- Reference solution with invariants

function Count(a: seq<int>, v: int): nat
{
  if |a| == 0 then 0
  else (if a[0] == v then 1 else 0) + Count(a[1..], v)
}

function CountTo(a: seq<int>, v: int, n: int): nat
  requires 0 <= n <= |a|
{
  if n == 0 then 0
  else (if a[n-1] == v then 1 else 0) + CountTo(a, v, n-1)
}

lemma CountToStep(a: seq<int>, v: int, n: int)
  requires 0 < n <= |a|
  ensures CountTo(a, v, n) == CountTo(a, v, n-1) + (if a[n-1] == v then 1 else 0)
{
  // Direct from definition
}

lemma CountToFull(a: seq<int>, v: int)
  ensures CountTo(a, v, |a|) == Count(a, v)
  decreases |a|
{
  if |a| == 0 {
  } else {
    CountToFull(a[1..], v);
    CountToSlice(a, v, |a|);
  }
}

lemma CountToSlice(a: seq<int>, v: int, n: int)
  requires 0 < n <= |a|
  ensures CountTo(a, v, n) == (if a[0] == v then 1 else 0) + CountTo(a[1..], v, n - 1)
  decreases n
{
  if n == 1 {
    assert CountTo(a, v, 1) == (if a[0] == v then 1 else 0) + CountTo(a, v, 0);
    assert CountTo(a[1..], v, 0) == 0;
  } else {
    CountToSlice(a, v, n - 1);
    // CountTo(a, v, n) = (if a[n-1] == v then 1 else 0) + CountTo(a, v, n-1)
    // By IH: CountTo(a, v, n-1) = (if a[0] == v then 1 else 0) + CountTo(a[1..], v, n-2)
    // CountTo(a[1..], v, n-1) = (if a[1..][n-2] == v then 1 else 0) + CountTo(a[1..], v, n-2)
    assert a[n-1] == a[1..][n-2];
  }
}

predicate IsMajority(a: seq<int>, v: int)
{
  Count(a, v) > |a| / 2
}

predicate HasMajority(a: seq<int>)
{
  exists v :: v in a && IsMajority(a, v)
}

method MajorityVote(a: seq<int>) returns (candidate: int)
  requires |a| > 0
  requires HasMajority(a)
  ensures candidate in a
  ensures IsMajority(a, candidate)
{
  // Phase 1: Find candidate
  candidate := a[0];
  var count := 1;
  var i := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant candidate in a
    invariant count >= 0
    decreases |a| - i
  {
    if a[i] == candidate {
      count := count + 1;
    } else if count == 0 {
      candidate := a[i];
      count := 1;
    } else {
      count := count - 1;
    }
    i := i + 1;
  }

  // Phase 2: Verify
  var actualCount := 0;
  i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant actualCount == CountTo(a, candidate, i)
    decreases |a| - i
  {
    if a[i] == candidate {
      actualCount := actualCount + 1;
    }
    i := i + 1;
  }
  CountToFull(a, candidate);
  if actualCount <= |a| / 2 {
    // candidate is wrong, but majority must exist
    // Find the true majority element by brute force
    var j := 0;
    while j < |a|
      invariant 0 <= j <= |a|
      invariant forall k :: 0 <= k < j ==> !IsMajority(a, a[k])
      decreases |a| - j
    {
      var c := 0;
      var m := 0;
      while m < |a|
        invariant 0 <= m <= |a|
        invariant c == CountTo(a, a[j], m)
        decreases |a| - m
      {
        if a[m] == a[j] {
          c := c + 1;
        }
        m := m + 1;
      }
      CountToFull(a, a[j]);
      if c > |a| / 2 {
        candidate := a[j];
        return;
      }
      j := j + 1;
    }
    // HasMajority guarantees we find one
    assert false;
  }
}
