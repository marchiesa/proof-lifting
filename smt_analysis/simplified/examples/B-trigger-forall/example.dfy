lemma linear_fixed(s: seq<int>, k: int)
  requires k > 0
  requires |s| > k + 1
  requires forall i :: 0 <= i < |s| ==> s[i] == i - k
  ensures exists i :: 0 <= i < |s| && s[i] > 0
{
  var _ := s[k + 1]; // essential
}
