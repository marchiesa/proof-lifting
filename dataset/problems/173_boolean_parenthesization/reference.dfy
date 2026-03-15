// Boolean Parenthesization -- Reference solution with invariants

method CountWaysTrue(symbols: seq<bool>, operators: seq<char>) returns (result: int)
  requires |symbols| > 0
  requires |operators| == |symbols| - 1
  requires forall i :: 0 <= i < |operators| ==> operators[i] == '&' || operators[i] == '|' || operators[i] == '^'
  ensures result >= 0
{
  var n := |symbols|;
  var T := new int[n, n];
  var F := new int[n, n];

  // Initialize everything to 0 first
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall a, b :: 0 <= a < i && 0 <= b < n ==> T[a, b] == 0 && F[a, b] == 0
    decreases n - i
  {
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant forall a, b :: 0 <= a < i && 0 <= b < n ==> T[a, b] == 0 && F[a, b] == 0
      invariant forall b :: 0 <= b < j ==> T[i, b] == 0 && F[i, b] == 0
      decreases n - j
    {
      T[i, j] := 0;
      F[i, j] := 0;
      j := j + 1;
    }
    i := i + 1;
  }

  // Set diagonal
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall a, b :: 0 <= a < n && 0 <= b < n ==> T[a, b] >= 0 && F[a, b] >= 0
    decreases n - i
  {
    T[i, i] := if symbols[i] then 1 else 0;
    F[i, i] := if symbols[i] then 0 else 1;
    i := i + 1;
  }

  var gap := 1;
  while gap < n
    invariant 1 <= gap <= n
    invariant forall a, b :: 0 <= a < n && 0 <= b < n ==> T[a, b] >= 0 && F[a, b] >= 0
    decreases n - gap
  {
    i := 0;
    while i + gap < n
      invariant 0 <= i
      invariant forall a, b :: 0 <= a < n && 0 <= b < n ==> T[a, b] >= 0 && F[a, b] >= 0
      decreases n - gap - i
    {
      var j := i + gap;
      T[i, j] := 0;
      F[i, j] := 0;
      var k := i;
      while k < j
        invariant i <= k <= j
        invariant T[i, j] >= 0 && F[i, j] >= 0
        invariant forall a, b :: 0 <= a < n && 0 <= b < n && (a != i || b != j) ==> T[a, b] >= 0 && F[a, b] >= 0
        decreases j - k
      {
        var tl := T[i, k];
        var fl := F[i, k];
        var tr := T[k+1, j];
        var fr := F[k+1, j];
        var op := operators[k];
        if op == '&' {
          T[i, j] := T[i, j] + tl * tr;
          // F += total*total - T_and = (tl+fl)*(tr+fr) - tl*tr
          // = tl*fr + fl*tr + fl*fr >= 0
          F[i, j] := F[i, j] + tl * fr + fl * tr + fl * fr;
        } else if op == '|' {
          F[i, j] := F[i, j] + fl * fr;
          // T += total*total - F_or = (tl+fl)*(tr+fr) - fl*fr
          // = tl*tr + tl*fr + fl*tr >= 0
          T[i, j] := T[i, j] + tl * tr + tl * fr + fl * tr;
        } else {
          T[i, j] := T[i, j] + tl * fr + fl * tr;
          F[i, j] := F[i, j] + tl * tr + fl * fr;
        }
        k := k + 1;
      }
      i := i + 1;
    }
    gap := gap + 1;
  }

  result := T[0, n - 1];
}
