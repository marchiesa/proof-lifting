lemma L(s: seq<int>)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  ensures exists k :: 0 <= k < |s| && s[k] >= 0
{
  assert s[0] >= 0;
}
