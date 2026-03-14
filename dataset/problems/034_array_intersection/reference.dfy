// Array Intersection of Two Sorted Arrays -- Reference solution with invariants

predicate StrictlySorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] < a[j]
}

predicate IsSubsetOf(a: seq<int>, b: seq<int>)
{
  forall x :: x in a ==> x in b
}

method Intersection(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires StrictlySorted(a)
  requires StrictlySorted(b)
  ensures StrictlySorted(result)
  ensures IsSubsetOf(result, a)
  ensures IsSubsetOf(result, b)
  ensures forall x :: x in a && x in b ==> x in result
{
  result := [];
  var i := 0;
  var j := 0;
  while i < |a| && j < |b|
    invariant 0 <= i <= |a|
    invariant 0 <= j <= |b|
    invariant StrictlySorted(result)
    invariant IsSubsetOf(result, a)
    invariant IsSubsetOf(result, b)
    invariant |result| > 0 && i < |a| ==> result[|result| - 1] < a[i]
    invariant |result| > 0 && j < |b| ==> result[|result| - 1] < b[j]
    invariant forall x :: x in a && x in b ==>
                (x in result) || ((exists ai :: i <= ai < |a| && a[ai] == x) && (exists bj :: j <= bj < |b| && b[bj] == x))
    decreases |a| - i + |b| - j
  {
    if a[i] == b[j] {
      result := result + [a[i]];
      i := i + 1;
      j := j + 1;
    } else if a[i] < b[j] {
      // a[i] < b[j], so for any x in b with x <= a[i], x is not in b[j..]
      // We skip a[i]. For the invariant: any x == a[i] that is in b must have
      // its b-occurrence at index < j (since a[i] < b[j] and b is sorted).
      // But then x is NOT in b[j..], so for the invariant to hold, x must be in result.
      // Is it? From the old invariant: x in result OR (x in a[i..] AND x in b[j..]).
      // x == a[i] is in a[i..]. x in b[j..]? x < b[j] and b sorted means NO.
      // So x must be in result from the old invariant... but x in a[i..] is true and x in b[j..] is false.
      // The disjunction says: in result OR (in a[i..] AND in b[j..]).
      // (in a[i..] AND in b[j..]) is false. So x in result. Good, but is this actually established?
      // From old invariant: x in result OR (x in a[old_i..] AND x in b[j..]).
      // x in a[old_i..] (since a[old_i] == x or x appears later).
      // If x == a[i]: x in b[j..] needs to be checked. x < b[j], so x not in b[j..].
      //   So from the old invariant: x in result.
      // After i++: need x in result OR (x in a[i+1..] AND x in b[j..]).
      //   x in result already. Done.
      // For other x in a, in b: old invariant gives x in result or (x in a[old_i..] and x in b[j..]).
      //   x in a[old_i..] ==> x in a[i+1..] or x == a[i].
      //   If x in a[i+1..] and x in b[j..]: fine.
      //   If x == a[i]: x in result (shown above). Fine.
      i := i + 1;
    } else {
      // symmetric
      j := j + 1;
    }
  }
  // After loop: i == |a| or j == |b|
  // Any x in a and in b: from invariant, x in result or (x in a[i..] and x in b[j..])
  // If i == |a|: a[i..] == [], so x not in a[i..], so x in result.
  // If j == |b|: b[j..] == [], so x not in b[j..], so x in result.
}
