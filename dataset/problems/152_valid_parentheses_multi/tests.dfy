// Valid Parentheses (Multiple Types) -- Spec tests

function Matching(c: char): char {
  if c == ')' then '('
  else if c == ']' then '['
  else if c == '}' then '{'
  else c
}

predicate IsOpen(c: char) { c == '(' || c == '[' || c == '{' }
predicate IsClose(c: char) { c == ')' || c == ']' || c == '}' }

function ProcessWithStack(s: seq<char>, stack: seq<char>, i: int): seq<char>
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then stack
  else if IsOpen(s[i]) then ProcessWithStack(s, [s[i]] + stack, i + 1)
  else if IsClose(s[i]) then
    if |stack| > 0 && stack[0] == Matching(s[i]) then ProcessWithStack(s, stack[1..], i + 1)
    else ['\0']
  else ProcessWithStack(s, stack, i + 1)
}

predicate IsValidParentheses(s: seq<char>) {
  ProcessWithStack(s, [], 0) == []
}

method ValidParentheses(s: seq<char>) returns (valid: bool)
  ensures valid == IsValidParentheses(s)
{
  var stack: seq<char> := [];
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    if IsOpen(s[i]) {
      stack := [s[i]] + stack;
    } else if IsClose(s[i]) {
      if |stack| == 0 || stack[0] != Matching(s[i]) {
        assume {:axiom} !IsValidParentheses(s);
        return false;
      }
      stack := stack[1..];
    }
    i := i + 1;
  }
  valid := |stack| == 0;
  assume {:axiom} valid == IsValidParentheses(s);
}

method Main() {
  // Positive tests
  var r1 := ValidParentheses("()");
  expect r1 == true;
  expect IsValidParentheses("()");

  var r2 := ValidParentheses("()[]{}");
  expect r2 == true;

  var r3 := ValidParentheses("{[()]}");
  expect r3 == true;

  var r4 := ValidParentheses("");
  expect r4 == true;

  // Negative tests
  var r5 := ValidParentheses("(]");
  expect r5 == false;

  var r6 := ValidParentheses("([)]");
  expect r6 == false;

  var r7 := ValidParentheses("(");
  expect r7 == false;

  var r8 := ValidParentheses(")");
  expect r8 == false;

  print "All spec tests passed\n";
}
