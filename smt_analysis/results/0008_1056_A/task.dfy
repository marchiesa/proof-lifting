ghost predicate InSeq(x: int, s: seq<int>)
{
  exists i | 0 <= i < |s| :: s[i] == x
}

// A line is possible iff it stops at every observed stop
ghost predicate PossibleLine(line: int, stops: seq<seq<int>>)
{
  forall k | 0 <= k < |stops| :: InSeq(line, stops[k])
}

method DetermineLine(stops: seq<seq<int>>) returns (result: seq<int>)
  // Soundness: every element in result is a possible line
  ensures forall i | 0 <= i < |result| :: PossibleLine(result[i], stops)
  // Completeness: every possible line appears in result
  ensures forall k | 0 <= k < |stops| :: forall j | 0 <= j < |stops[k]| ::
            PossibleLine(stops[k][j], stops) ==> InSeq(stops[k][j], result)
{
  if |stops| == 0 { result := []; return; }
  result := stops[0];
  for k := 1 to |stops| {
    var newResult: seq<int> := [];
    for i := 0 to |result| {
      var found := false;
      for j := 0 to |stops[k]| {
        if result[i] == stops[k][j] {
          found := true;
        }
      }
      if found {
        newResult := newResult + [result[i]];
      }
    }
    result := newResult;
  }
}

method SameElements(a: seq<int>, b: seq<int>) returns (same: bool)
{
  if |a| != |b| { return false; }
  for i := 0 to |a| {
    var found := false;
    for j := 0 to |b| {
      if a[i] == b[j] { found := true; }
    }
    if !found { return false; }
  }
  for i := 0 to |b| {
    var found := false;
    for j := 0 to |a| {
      if b[i] == a[j] { found := true; }
    }
    if !found { return false; }
  }
  return true;
}