ghost function RemoveAt(s: string, idx: nat): string
  requires idx < |s|
{
  s[..idx] + s[idx + 1..]
}

ghost function InsertAt(s: string, idx: nat, c: char): string
  requires idx <= |s|
{
  s[..idx] + [c] + s[idx..]
}

ghost function TotalLength(strings: seq<string>): nat
  decreases |strings|
{
  if |strings| == 0 then 0
  else TotalLength(strings[..|strings| - 1]) + |strings[|strings| - 1]|
}

ghost predicate AllEqual(strings: seq<string>)
{
  forall i :: 0 <= i < |strings| ==> forall j :: 0 <= j < |strings| ==> strings[i] == strings[j]
}

// A legal move removes a character from string si at position sp
// and inserts it into string di at position dp.
// CanReachAllEqual returns true iff, starting from 'state', there exists
// a sequence of at most 'steps' legal moves leading to a configuration
// where all strings are equal.
ghost predicate CanReachAllEqual(state: seq<string>, steps: nat)
  decreases steps
{
  AllEqual(state) ||
  (steps > 0 &&
   exists si | 0 <= si < |state| ::
     exists sp | 0 <= sp < |state[si]| ::
       exists di | 0 <= di < |state| ::
         var ch := state[si][sp];
         var afterRemove := state[si := RemoveAt(state[si], sp)];
         exists dp | 0 <= dp <= |afterRemove[di]| ::
           CanReachAllEqual(afterRemove[di := InsertAt(afterRemove[di], dp, ch)], steps - 1))
}

method JugglingLetters(n: int, strings: seq<string>) returns (result: bool)
  requires n > 0
  requires n == |strings|
  ensures result == CanReachAllEqual(strings, TotalLength(strings))
{
  var allChars: seq<char> := [];
  var i := 0;
  while i < |strings| {
    var j := 0;
    while j < |strings[i]| {
      allChars := allChars + [strings[i][j]];
      j := j + 1;
    }
    i := i + 1;
  }

  result := true;
  i := 0;
  while i < |allChars| {
    var count := 0;
    var j := 0;
    while j < |allChars| {
      if allChars[j] == allChars[i] {
        count := count + 1;
      }
      j := j + 1;
    }
    if count % n != 0 {
      result := false;
      return;
    }
    i := i + 1;
  }
}