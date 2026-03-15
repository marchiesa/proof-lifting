// Boolean Parenthesization (count ways to parenthesize to get True)
// Task: Add loop invariants so that Dafny can verify this program.

// symbols: seq of booleans, operators: seq of chars ('&', '|', '^')
// |operators| == |symbols| - 1
method CountWaysTrue(symbols: seq<bool>, operators: seq<char>) returns (result: int)
  requires |symbols| > 0
  requires |operators| == |symbols| - 1
  requires forall i :: 0 <= i < |operators| ==> operators[i] == '&' || operators[i] == '|' || operators[i] == '^'
  ensures result >= 0
{
  var n := |symbols|;
  var T := new int[n, n];
  var F := new int[n, n];

  // Initialize everything to 0
  var i := 0;
  while i < n
  {
    var j := 0;
    while j < n
    {
      T[i, j] := 0;
      F[i, j] := 0;
      j := j + 1;
    }
    i := i + 1;
  }

  // Base case: single symbols
  i := 0;
  while i < n
  {
    T[i, i] := if symbols[i] then 1 else 0;
    F[i, i] := if symbols[i] then 0 else 1;
    i := i + 1;
  }

  // Fill for increasing gap
  var gap := 1;
  while gap < n
  {
    i := 0;
    while i + gap < n
    {
      var j := i + gap;
      T[i, j] := 0;
      F[i, j] := 0;
      var k := i;
      while k < j
      {
        var tl := T[i, k];
        var fl := F[i, k];
        var tr := T[k+1, j];
        var fr := F[k+1, j];
        var op := operators[k];
        if op == '&' {
          T[i, j] := T[i, j] + tl * tr;
          F[i, j] := F[i, j] + tl * fr + fl * tr + fl * fr;
        } else if op == '|' {
          F[i, j] := F[i, j] + fl * fr;
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
