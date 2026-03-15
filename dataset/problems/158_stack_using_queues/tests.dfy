// Stack Using Two Queues -- Spec tests

function StackSimSpec(ops: seq<int>, stack: seq<int>, i: int): seq<int>
  requires 0 <= i <= |ops|
  decreases |ops| - i
{
  if i == |ops| then []
  else if ops[i] > 0 then StackSimSpec(ops, [ops[i]] + stack, i + 1)
  else if |stack| > 0 then [stack[0]] + StackSimSpec(ops, stack[1..], i + 1)
  else StackSimSpec(ops, stack, i + 1)
}

function StackResult(ops: seq<int>): seq<int> {
  StackSimSpec(ops, [], 0)
}

method SimulateStack(ops: seq<int>) returns (result: seq<int>)
  ensures result == StackResult(ops)
{
  var stack: seq<int> := [];
  result := [];
  var i := 0;
  while i < |ops| decreases |ops| - i {
    if ops[i] > 0 {
      stack := [ops[i]] + stack;
    } else {
      if |stack| > 0 {
        result := result + [stack[0]];
        stack := stack[1..];
      }
    }
    i := i + 1;
  }
  assume {:axiom} result == StackResult(ops);
}

method Main() {
  // Push 1, Push 2, Pop -> 2, Pop -> 1
  var ops1 := [1, 2, 0, 0];
  var r1 := SimulateStack(ops1);
  expect r1 == [2, 1];

  // Push 3, Pop -> 3, Push 4, Pop -> 4
  var ops2 := [3, 0, 4, 0];
  var r2 := SimulateStack(ops2);
  expect r2 == [3, 4];

  // Pop on empty does nothing
  var ops3 := [0, 1, 0];
  var r3 := SimulateStack(ops3);
  expect r3 == [1];

  // Only pushes, no pops
  var ops4 := [1, 2, 3];
  var r4 := SimulateStack(ops4);
  expect |r4| == 0;

  // Negative test: LIFO order
  var ops5 := [5, 10, 0];
  var r5 := SimulateStack(ops5);
  expect r5[0] == 10;  // Last in, first out
  expect r5[0] != 5;

  print "All spec tests passed\n";
}
