// Run-Length Compress -- Reference solution with invariants

function Expand(vals: seq<int>, counts: seq<nat>): seq<int>
  requires |vals| == |counts|
  decreases |vals|
{
  if |vals| == 0 then []
  else Repeat(vals[0], counts[0]) + Expand(vals[1..], counts[1..])
}

function Repeat(v: int, n: nat): seq<int>
  decreases n
{
  if n == 0 then [] else [v] + Repeat(v, n - 1)
}

predicate NoAdjacentDups(vals: seq<int>)
{
  forall i :: 0 <= i < |vals| - 1 ==> vals[i] != vals[i + 1]
}

predicate AllPositive(counts: seq<nat>)
{
  forall i :: 0 <= i < |counts| ==> counts[i] > 0
}

lemma RepeatAppend(v: int, n: nat)
  requires n > 0
  ensures Repeat(v, n) + [v] == Repeat(v, n + 1)
  decreases n
{
  if n == 1 {
    assert Repeat(v, 1) == [v];
    assert Repeat(v, 1) + [v] == [v, v];
    assert Repeat(v, 2) == [v] + Repeat(v, 1) == [v] + [v] == [v, v];
  } else {
    RepeatAppend(v, n - 1);
    assert Repeat(v, n) == [v] + Repeat(v, n - 1);
    calc {
      Repeat(v, n) + [v];
      == ([v] + Repeat(v, n - 1)) + [v];
      == [v] + (Repeat(v, n - 1) + [v]);
      == [v] + Repeat(v, n);
      == Repeat(v, n + 1);
    }
  }
}

lemma ExpandLastIncrement(vals: seq<int>, counts: seq<nat>, v: int)
  requires |vals| == |counts| > 0
  requires vals[|vals| - 1] == v
  requires AllPositive(counts)
  ensures Expand(vals, counts[..|counts| - 1] + [counts[|counts| - 1] + 1])
       == Expand(vals, counts) + [v]
  decreases |vals|
{
  if |vals| == 1 {
    assert vals == [v];
    var newCounts := counts[..|counts| - 1] + [counts[0] + 1];
    assert newCounts == [counts[0] + 1];
    RepeatAppend(v, counts[0]);
    assert Repeat(v, counts[0] + 1) == Repeat(v, counts[0]) + [v];
    assert Expand([v], [counts[0] + 1]) == Repeat(v, counts[0] + 1) + Expand([], []);
    assert Expand([], []) == [];
  } else {
    var newCounts := counts[..|counts| - 1] + [counts[|counts| - 1] + 1];
    assert newCounts[0] == counts[0];
    assert newCounts[1..] == counts[1..|counts| - 1] + [counts[|counts| - 1] + 1];
    assert counts[1..][..|counts[1..]| - 1] == counts[1..|counts| - 1];
    ExpandLastIncrement(vals[1..], counts[1..], v);
    assert Expand(vals[1..], newCounts[1..]) == Expand(vals[1..], counts[1..]) + [v];
    calc {
      Expand(vals, newCounts);
      == Repeat(vals[0], newCounts[0]) + Expand(vals[1..], newCounts[1..]);
      == Repeat(vals[0], counts[0]) + (Expand(vals[1..], counts[1..]) + [v]);
      == (Repeat(vals[0], counts[0]) + Expand(vals[1..], counts[1..])) + [v];
      == Expand(vals, counts) + [v];
    }
  }
}

lemma ExpandAppendNew(vals: seq<int>, counts: seq<nat>, v: int)
  requires |vals| == |counts|
  ensures Expand(vals + [v], counts + [1]) == Expand(vals, counts) + [v]
  decreases |vals|
{
  if |vals| == 0 {
    assert vals + [v] == [v];
    assert counts + [1] == [1];
    assert Expand([v], [1]) == Repeat(v, 1) + Expand([], []);
    assert Repeat(v, 1) == [v] + Repeat(v, 0) == [v] + [] == [v];
    assert Expand([], []) == [];
  } else {
    assert (vals + [v])[0] == vals[0];
    assert (vals + [v])[1..] == vals[1..] + [v];
    assert (counts + [1])[0] == counts[0];
    assert (counts + [1])[1..] == counts[1..] + [1];
    ExpandAppendNew(vals[1..], counts[1..], v);
  }
}

method Compress(s: seq<int>) returns (vals: seq<int>, counts: seq<nat>)
  ensures |vals| == |counts|
  ensures NoAdjacentDups(vals)
  ensures AllPositive(counts)
  ensures Expand(vals, counts) == s
{
  if |s| == 0 {
    return [], [];
  }
  vals := [s[0]];
  counts := [1];
  var i := 1;
  while i < |s|
    invariant 1 <= i <= |s|
    invariant |vals| == |counts| > 0
    invariant NoAdjacentDups(vals)
    invariant AllPositive(counts)
    invariant Expand(vals, counts) == s[..i]
    invariant vals[|vals| - 1] == s[i - 1]
    decreases |s| - i
  {
    assert s[..i+1] == s[..i] + [s[i]];
    if s[i] == vals[|vals| - 1] {
      ExpandLastIncrement(vals, counts, s[i]);
      counts := counts[..|counts| - 1] + [counts[|counts| - 1] + 1];
    } else {
      ExpandAppendNew(vals, counts, s[i]);
      vals := vals + [s[i]];
      counts := counts + [1];
    }
    i := i + 1;
  }
  assert s[..|s|] == s;
}
