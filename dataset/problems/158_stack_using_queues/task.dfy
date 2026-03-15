// Implement Stack Using Two Queues (seq-based simulation)
// Task: Add loop invariants so that Dafny can verify this program.

// Spec: model ideal stack behavior
// ops[i] > 0 means push ops[i], ops[i] == 0 means pop
function StackSimSpec(ops: seq<int>, stack: seq<int>, i: int): seq<int>
  requires 0 <= i <= |ops|
  decreases |ops| - i
{
  if i == |ops| then []
  else if ops[i] > 0 then StackSimSpec(ops, [ops[i]] + stack, i + 1)
  else if |stack| > 0 then [stack[0]] + StackSimSpec(ops, stack[1..], i + 1)
  else StackSimSpec(ops, stack, i + 1) // pop on empty: skip
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
  while i < |ops|
  {
    if ops[i] > 0 {
      // Push: add to front of stack
      stack := [ops[i]] + stack;
    } else {
      if |stack| > 0 {
        result := result + [stack[0]];
        stack := stack[1..];
      }
    }
    i := i + 1;
  }
}
