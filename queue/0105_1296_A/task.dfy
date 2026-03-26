ghost function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

// Can we reach an array with odd element-sum from 'source' by performing
// at most 'steps' copy operations (a[i] := a[j] where i != j)?
ghost predicate CanAchieveOddSumIn(source: seq<int>, steps: nat)
  decreases steps
{
  if Sum(source) % 2 != 0 then true
  else if steps == 0 then false
  else exists i | 0 <= i < |source| :: exists j | 0 <= j < |source| ::
    i != j && source[i] != source[j] &&
    CanAchieveOddSumIn(source[i := source[j]], steps - 1)
}

method ArrayWithOddSum(a: seq<int>) returns (result: bool)
  ensures result == CanAchieveOddSumIn(a, |a|)
{
  var sm := 0;
  for i := 0 to |a| {
    sm := sm + a[i];
  }
  if sm % 2 != 0 {
    result := true;
  } else {
    var od := 0;
    var ev := 0;
    for i := 0 to |a| {
      if a[i] % 2 != 0 {
        od := od + 1;
      } else {
        ev := ev + 1;
      }
    }
    if od == 0 || ev == 0 {
      result := false;
    } else {
      result := true;
    }
  }
}