// Pattern: Tokenize/parse a sequence into categories
// Source: aroberge/experimental/translate (tokenize source code)
//         puni/Note._expand_url (parse URL components)
// Real-world: lexing, CSV parsing, command line argument parsing

// Token types: 0=number, 1=operator, 2=unknown
method Tokenize(chars: seq<int>) returns (types: seq<int>)
  ensures |types| == |chars|
  ensures forall i :: 0 <= i < |types| ==> 0 <= types[i] <= 2
  ensures forall i :: 0 <= i < |chars| ==>
    (0 <= chars[i] <= 9 ==> types[i] == 0) &&
    (chars[i] == 43 || chars[i] == 45 ==> types[i] == 1) &&  // +, -
    (!(0 <= chars[i] <= 9) && chars[i] != 43 && chars[i] != 45 ==> types[i] == 2)
{
  types := [];
  var i := 0;
  while i < |chars|
    invariant 0 <= i <= |chars|
    invariant |types| == i
    invariant forall j :: 0 <= j < i ==> 0 <= types[j] <= 2
    invariant forall j :: 0 <= j < i ==>
      (0 <= chars[j] <= 9 ==> types[j] == 0) &&
      (chars[j] == 43 || chars[j] == 45 ==> types[j] == 1) &&
      (!(0 <= chars[j] <= 9) && chars[j] != 43 && chars[j] != 45 ==> types[j] == 2)
  {
    var t := 2;  // default: unknown
    if 0 <= chars[i] <= 9 {
      t := 0;
    } else if chars[i] == 43 || chars[i] == 45 {
      t := 1;
    }
    types := types + [t];
    i := i + 1;
  }
}
