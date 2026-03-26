
predicate P(x: nat)
predicate G(x: nat)

function f(n: nat): nat
{
  n+1
}
function g(n: nat): nat
{
  n+1
}

lemma Obvious1(n: nat, m: nat)
  requires exists k | n <= k < m :: P(f(k))
  ensures exists k | n <= k < m :: P(g(k))
{
  // Fails without these, any one of these assertions is sufficient:
  //   assert forall k :: f(k) == g(k);
  // assert exists k {:trigger f(k)} | n <= k < m :: P(g(k));
  // assert exists k | n <= k < m :: P(g(k)) by {
  //   var k :| n <= k < m && P(f(k));
  //   assert P(g(k));
  // }
}
lemma Obvious2(n: nat, m: nat)
  requires exists k | n <= k < m :: P(f(k))
  ensures exists k | n+1 <= k < m+1 :: P(k)
{
  //This one verifies automatically
}
lemma Obvious3(n: nat, m: nat)
  requires exists k | n+1 <= k < m+1 :: P(k)
  ensures exists k | n <= k < m :: P(f(k))
{
  var k :| n+1 <= k < m+1 && P(k);
  var _ := f(k-1);
}

method m(s: seq<nat>)
  requires exists k | 0 <= k < |s| :: P(s[k])
  requires forall k | 0 <= k < |s| :: P(s[k]) ==> 0 <= k < |s|-1 && G(s[k+1])
{
  assert |s| >= 1;
  var c := 0;
  var i := if P(s[c]) then |s| else 1;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= c < i
    invariant forall k | 0 <= k < c :: !P(s[k])
    invariant P(s[c]) ==> i == |s|
    invariant !P(s[c]) ==> i == c+1
  {
    c := i;
    if P(s[i]) {
      i := |s|;
    } else {
      i := i+1;
    }
  }
  assert P(s[c]);
}


predicate RowProperty(r: seq<int>)

method findFirst<T>(s: seq<T>, p: T -> bool) returns (idx: nat)
  requires exists k | 0 <= k < |s| :: p(s[k])
  ensures 0 <= idx < |s|
  ensures p(s[idx])
  ensures forall j | 0 <= j < |s| :: p(s[j]) ==> idx <= j
{
  assert |s| >= 1;
  var c := 0;
  var i := if p(s[c]) then |s| else 1;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= c < i
    invariant forall k | 0 <= k < c :: !p(s[k])
    invariant p(s[c]) ==> i == |s|
    invariant !p(s[c]) ==> i == c+1
  {
    c := i;
    if p(s[i]) {
      i := |s|;
    } else {
      i := i+1;
    }
  }
  assert p(s[c]);
  return c;
}

predicate Contains<T>(s: seq<T>, p: T -> bool)
{
  exists k | 0 <= k < |s| :: p(s[k])
}

method index_offset(s: seq<nat>)
  requires exists k | 1 <= k < |s| :: P(s[k])
  ensures exists k {:trigger s[k+1]} | 0 <= k < |s|-1 :: P(s[k+1])
{
  // Fails without explicitly constructing a witness.
  var k :| 1 <= k < |s| && P(s[k]);
  var k' := k-1;
  var _ :=  P(s[k'+1]);
}

method smallest_with_witness<T>(s: seq<T>, p: T -> bool) returns (l: nat)
  requires Contains<T>(s, p)
  ensures 0 <= l <= |s| && Contains<T>(s[..l], p)
  // ensures forall k | 0 <= k < |s| :: Contains<T>(s[..k], p) ==> l <= k
{
  var idx := findFirst<T>(s, p);
  // assert Contains<T>(s[..idx+1], p);
  return idx+1;
}
