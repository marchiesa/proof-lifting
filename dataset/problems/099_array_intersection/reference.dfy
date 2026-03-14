// Intersection of Two Arrays -- Reference solution with invariants

predicate InSeq(a: seq<int>, x: int)
{
  exists i :: 0 <= i < |a| && a[i] == x
}

predicate IsSubsetOf(a: seq<int>, b: seq<int>)
{
  forall i :: 0 <= i < |a| ==> InSeq(b, a[i])
}

predicate NoDuplicates(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] != a[j]
}

lemma InSeqAppend(s: seq<int>, x: int, y: int)
  requires InSeq(s, x)
  ensures InSeq(s + [y], x)
{
  var idx :| 0 <= idx < |s| && s[idx] == x;
  assert (s + [y])[idx] == x;
}

lemma InSeqExtend(s: seq<int>, y: int)
  ensures InSeq(s + [y], y)
{
  var t := s + [y];
  assert t[|s|] == y;
}

method FindInSeq(s: seq<int>, x: int) returns (found: bool)
  ensures found <==> InSeq(s, x)
{
  found := false;
  var j := 0;
  while j < |s|
    invariant 0 <= j <= |s|
    invariant found <==> exists k :: 0 <= k < j && s[k] == x
    decreases |s| - j
  {
    if s[j] == x {
      found := true;
      return;
    }
    j := j + 1;
  }
}

method Intersection(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  ensures IsSubsetOf(result, a)
  ensures IsSubsetOf(result, b)
  ensures NoDuplicates(result)
  ensures forall x :: InSeq(a, x) && InSeq(b, x) ==> InSeq(result, x)
{
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant IsSubsetOf(result, a)
    invariant IsSubsetOf(result, b)
    invariant NoDuplicates(result)
    invariant forall x :: InSeq(a[..i], x) && InSeq(b, x) ==> InSeq(result, x)
    decreases |a| - i
  {
    var inB := FindInSeq(b, a[i]);
    var inResult := FindInSeq(result, a[i]);

    if inB && !inResult {
      ghost var oldResult := result;
      result := result + [a[i]];

      // IsSubsetOf(result, a)
      assert IsSubsetOf(result, a) by {
        forall idx | 0 <= idx < |result|
          ensures InSeq(a, result[idx])
        {
          if idx < |oldResult| {
            assert result[idx] == oldResult[idx];
          } else {
            assert result[idx] == a[i];
            assert 0 <= i < |a| && a[i] == a[i];
          }
        }
      }

      // NoDuplicates
      assert NoDuplicates(result) by {
        forall p, q | 0 <= p < q < |result|
          ensures result[p] != result[q]
        {
          if q < |oldResult| {
          } else {
            assert result[q] == a[i];
            assert !InSeq(oldResult, a[i]);
            assert result[p] == oldResult[p];
            if result[p] == a[i] {
              assert InSeq(oldResult, a[i]);
              assert false;
            }
          }
        }
      }

      // Completeness
      assert forall x :: InSeq(a[..i+1], x) && InSeq(b, x) ==> InSeq(result, x) by {
        forall x | InSeq(a[..i+1], x) && InSeq(b, x)
          ensures InSeq(result, x)
        {
          if x == a[i] {
            InSeqExtend(oldResult, a[i]);
          } else if InSeq(a[..i], x) {
            assert InSeq(oldResult, x);
            InSeqAppend(oldResult, x, a[i]);
          } else {
            assert a[..i+1] == a[..i] + [a[i]];
            var w :| 0 <= w < |a[..i+1]| && a[..i+1][w] == x;
            if w < i { assert a[..i][w] == x; assert InSeq(a[..i], x); }
            assert x == a[i];
            assert false;
          }
        }
      }
    } else {
      // Completeness preserved
      assert forall x :: InSeq(a[..i+1], x) && InSeq(b, x) ==> InSeq(result, x) by {
        forall x | InSeq(a[..i+1], x) && InSeq(b, x)
          ensures InSeq(result, x)
        {
          assert a[..i+1] == a[..i] + [a[i]];
          if InSeq(a[..i], x) {
          } else {
            var w :| 0 <= w < |a[..i+1]| && a[..i+1][w] == x;
            if w < i { assert a[..i][w] == x; assert InSeq(a[..i], x); assert false; }
            assert x == a[i];
            if !inB {
              assert !InSeq(b, x);
              assert false;
            } else {
              // inResult is true, so a[i] is already in result
              assert InSeq(result, a[i]);
            }
          }
        }
      }
    }
    i := i + 1;
  }
  assert a[..|a|] == a;
}
