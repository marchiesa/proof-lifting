// Problem 5: Map/Set Reasoning Gaps — Histogram

function CountIn(s: seq<int>, x: int): nat
{
  if |s| == 0 then 0
  else (if s[0] == x then 1 else 0) + CountIn(s[1..], x)
}

lemma CountInAppend(s: seq<int>, elem: int, x: int)
  ensures CountIn(s + [elem], x) == CountIn(s, x) + (if elem == x then 1 else 0)
{
  if |s| == 0 {
    assert s + [elem] == [elem];
  } else {
    assert (s + [elem])[0] == s[0];
    assert (s + [elem])[1..] == s[1..] + [elem];
    CountInAppend(s[1..], elem, x);
  }
}

lemma CountInNotIn(s: seq<int>, x: int)
  requires x !in s
  ensures CountIn(s, x) == 0
{
  if |s| == 0 {
  } else {
    assert s[0] != x;
    assert x !in s[1..];
    CountInNotIn(s[1..], x);
  }
}

method Histogram(s: seq<int>) returns (hist: map<int, nat>)
  ensures forall x :: x in hist <==> x in s
  ensures forall x :: x in hist ==> hist[x] == CountIn(s, x)
{
  hist := map[];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall x :: x in hist <==> x in s[..i]
    invariant forall x :: x in hist ==> hist[x] == CountIn(s[..i], x)
  {
    var key := s[i];
    assert s[..i+1] == s[..i] + [key];
    // Update count for the key
    if key in hist {
      forall x | x in hist && x != key
        ensures CountIn(s[..i+1], x) == CountIn(s[..i], x)
      {
        CountInAppend(s[..i], key, x);
      }
      CountInAppend(s[..i], key, key);
      hist := hist[key := hist[key] + 1];
    } else {
      CountInNotIn(s[..i], key);
      CountInAppend(s[..i], key, key);
      forall x | x in hist
        ensures CountIn(s[..i+1], x) == CountIn(s[..i], x)
      {
        CountInAppend(s[..i], key, x);
      }
      hist := hist[key := 1];
    }
    i := i + 1;
  }
  assert s[..i] == s;
}
