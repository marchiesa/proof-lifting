// Generate All Subsets of Size K (iterative)
// Task: Add loop invariants so that Dafny can verify this program.

predicate StrictlySorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

predicate ValidSubset(s: seq<int>, n: int) {
  StrictlySorted(s) &&
  forall i :: 0 <= i < |s| ==> 0 <= s[i] < n
}

predicate AllSizeK(result: seq<seq<int>>, k: int) {
  forall i :: 0 <= i < |result| ==> |result[i]| == k
}

predicate AllValid(result: seq<seq<int>>, n: int) {
  forall i :: 0 <= i < |result| ==> ValidSubset(result[i], n)
}

predicate NoDuplicates(result: seq<seq<int>>) {
  forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
}

method SubsetsOfSizeK(n: int, k: int) returns (result: seq<seq<int>>)
  requires 0 <= k <= n
  ensures AllSizeK(result, k)
  ensures AllValid(result, n)
  ensures NoDuplicates(result)
{
  if k == 0 {
    result := [[]];
    return;
  }
  result := [];
  var combo: seq<int> := [];
  var i := 0;
  while i < k
  {
    combo := combo + [i];
    i := i + 1;
  }

  while true
  {
    result := result + [combo];
    var pos := k - 1;
    while pos >= 0 && combo[pos] == n - k + pos
    {
      pos := pos - 1;
    }
    if pos < 0 { break; }
    combo := combo[pos := combo[pos] + 1];
    var j := pos + 1;
    while j < k
    {
      combo := combo[j := combo[j-1] + 1];
      j := j + 1;
    }
  }
}
