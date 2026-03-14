// Run-Length Encoding -- Reference solution with invariants

// Repeat a value n times
function Repeat(v: int, n: int): seq<int>
  requires n > 0
  decreases n
{
  if n == 1 then [v]
  else [v] + Repeat(v, n - 1)
}

lemma RepeatLength(v: int, n: int)
  requires n > 0
  ensures |Repeat(v, n)| == n
  decreases n
{
  if n > 1 {
    RepeatLength(v, n - 1);
  }
}

lemma RepeatAppend(v: int, n: int)
  requires n > 0
  ensures Repeat(v, n) + [v] == Repeat(v, n + 1)
  decreases n
{
  if n > 1 {
    calc {
      Repeat(v, n) + [v];
      == [v] + Repeat(v, n - 1) + [v];
      == { RepeatAppend(v, n - 1); }
      [v] + Repeat(v, n);
      == Repeat(v, n + 1);
    }
  }
}

// Expand an RLE encoding back to the original sequence
function Expand(values: seq<int>, counts: seq<int>): seq<int>
  requires |values| == |counts|
  requires forall i :: 0 <= i < |counts| ==> counts[i] > 0
  decreases |values|
{
  if |values| == 0 then []
  else Repeat(values[0], counts[0]) + Expand(values[1..], counts[1..])
}

lemma ExpandAppend(values: seq<int>, counts: seq<int>, v: int)
  requires |values| == |counts|
  requires forall i :: 0 <= i < |counts| ==> counts[i] > 0
  ensures Expand(values + [v], counts + [1]) == Expand(values, counts) + [v]
  decreases |values|
{
  if |values| == 0 {
    assert values + [v] == [v];
    assert counts + [1] == [1];
  } else {
    assert (values + [v])[0] == values[0];
    assert (counts + [1])[0] == counts[0];
    assert (values + [v])[1..] == values[1..] + [v];
    assert (counts + [1])[1..] == counts[1..] + [1];
    ExpandAppend(values[1..], counts[1..], v);
  }
}

lemma ExpandIncrementLast(values: seq<int>, counts: seq<int>)
  requires |values| == |counts| > 0
  requires forall i :: 0 <= i < |counts| ==> counts[i] > 0
  ensures var newCounts := counts[|counts| - 1 := counts[|counts| - 1] + 1];
          (forall i :: 0 <= i < |newCounts| ==> newCounts[i] > 0) &&
          Expand(values, newCounts) == Expand(values, counts) + [values[|values| - 1]]
  decreases |values|
{
  var newCounts := counts[|counts| - 1 := counts[|counts| - 1] + 1];
  if |values| == 1 {
    assert newCounts == [counts[0] + 1];
    RepeatAppend(values[0], counts[0]);
  } else {
    assert values[1..] == values[1..];
    assert newCounts[0] == counts[0];
    assert newCounts[1..] == counts[1..][|counts[1..]| - 1 := counts[1..][|counts[1..]| - 1] + 1];
    ExpandIncrementLast(values[1..], counts[1..]);
  }
}

method RLE(a: seq<int>) returns (values: seq<int>, counts: seq<int>)
  ensures |values| == |counts|
  ensures forall i :: 0 <= i < |counts| ==> counts[i] > 0
  ensures forall i :: 0 <= i < |values| - 1 ==> values[i] != values[i + 1]
  ensures Expand(values, counts) == a
{
  if |a| == 0 {
    values := [];
    counts := [];
    return;
  }

  values := [a[0]];
  counts := [1];
  var i := 1;

  while i < |a|
    invariant 1 <= i <= |a|
    invariant |values| == |counts| >= 1
    invariant forall k :: 0 <= k < |counts| ==> counts[k] > 0
    invariant forall k :: 0 <= k < |values| - 1 ==> values[k] != values[k + 1]
    invariant values[|values| - 1] == a[i - 1]
    invariant Expand(values, counts) == a[..i]
    decreases |a| - i
  {
    if a[i] == values[|values| - 1] {
      ExpandIncrementLast(values, counts);
      counts := counts[|counts| - 1 := counts[|counts| - 1] + 1];
      assert Expand(values, counts) == a[..i] + [a[i]];
    } else {
      ExpandAppend(values, counts, a[i]);
      values := values + [a[i]];
      counts := counts + [1];
    }
    assert a[..i+1] == a[..i] + [a[i]];
    i := i + 1;
  }
  assert a[..i] == a;
}
