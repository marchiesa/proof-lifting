// Pattern: Reverse a sequence
// Source: common utility in many libraries (sorting, display, undo stacks)
// Real-world: stack operations, string reversal, undo history

method Reverse(a: seq<int>) returns (result: seq<int>)
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |a| ==> result[i] == a[|a| - 1 - i]
{
  result := [];
  var i := |a|;
  while i > 0
    invariant 0 <= i <= |a|
    invariant |result| == |a| - i
    invariant forall j :: 0 <= j < |a| - i ==> result[j] == a[|a| - 1 - j]
  {
    i := i - 1;
    assert forall j :: 0 <= j < |result| ==> result[j] == a[|a| - 1 - j];
    result := result + [a[i]];
    // After append, old elements keep their values
    assert result[|result|-1] == a[i];  // SMT QUIRK: property of appended element
  }
}
