// Pattern: Find element satisfying compound condition with existential postcondition
// Source: imcut/__ordered_values_by_indexes (find values matching multi-criteria)
//         database query with multiple WHERE clauses
// Real-world: multi-criteria search, constraint satisfaction, resource matching

predicate Eligible(age: int, score: int)
{
  age >= 18 && score >= 70
}

method FindEligible(ages: seq<int>, scores: seq<int>) returns (found: bool, idx: int)
  requires |ages| == |scores|
  ensures found ==> 0 <= idx < |ages| && Eligible(ages[idx], scores[idx])
  ensures !found ==> forall i :: 0 <= i < |ages| ==> !Eligible(ages[i], scores[i])
{
  found := false;
  idx := -1;
  var i := 0;
  while i < |ages|
    invariant 0 <= i <= |ages|
    invariant !found ==> forall j :: 0 <= j < i ==> !Eligible(ages[j], scores[j])
    invariant found ==> 0 <= idx < |ages| && Eligible(ages[idx], scores[idx])
  {
    if Eligible(ages[i], scores[i]) {
      assert Eligible(ages[i], scores[i]);  // SMT QUIRK: A2 predicate instantiation
      found := true;
      idx := i;
      return;
    }
    i := i + 1;
  }
}
