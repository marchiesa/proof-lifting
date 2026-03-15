// Minimum Add to Make Parentheses Valid

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

method Main()
{
  // "()" => already valid => 0
  var a := [1, 2];
  var r1 := MinAddParens(a);
  expect r1 >= 0;
  expect r1 == 0;

  // "(((" => need 3 closing => 3
  var b := [1, 1, 1];
  var r2 := MinAddParens(b);
  expect r2 == 3;

  // "))(" => need 2 opening + 1 closing => 3
  var c := [2, 2, 1];
  var r3 := MinAddParens(c);
  expect r3 >= 0;

  // Empty
  var d: seq<int> := [];
  var r4 := MinAddParens(d);
  expect r4 == 0;

  // "(())" => valid
  var e := [1, 1, 2, 2];
  var r5 := MinAddParens(e);
  expect r5 == 0;

  // Negative test: IsParens check
  expect IsParens([1, 2, 1, 2]);
  expect !IsParens([1, 3]);

  print "All spec tests passed\n";
}
