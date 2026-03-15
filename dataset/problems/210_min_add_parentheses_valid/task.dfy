// Minimum Add to Make Parentheses Valid
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsParens(s: seq<int>)
{
  forall i :: 0 <= i < |s| ==> s[i] == 1 || s[i] == 2
}

method MinAddParens(s: seq<int>) returns (result: int)
  requires IsParens(s)
  ensures result >= 0
{
  var open := 0;   // unmatched '('
  var close := 0;  // unmatched ')'
  var i := 0;
  while i < |s|
  {
    if s[i] == 1 {
      open := open + 1;
    } else {
      if open > 0 {
        open := open - 1;
      } else {
        close := close + 1;
      }
    }
    i := i + 1;
  }
  result := open + close;
}
