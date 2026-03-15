// Stack Using Two Queues -- Reference solution with invariants

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

lemma StackSimAppend(ops: seq<int>, stack: seq<int>, i: int, prefix: seq<int>)
  requires 0 <= i <= |ops|
  ensures prefix + StackSimSpec(ops, stack, i) == prefix + StackSimSpec(ops, stack, i)
{
}

method SimulateStack(ops: seq<int>) returns (result: seq<int>)
  ensures result == StackResult(ops)
{
  var stack: seq<int> := [];
  result := [];
  var i := 0;
  while i < |ops|
    invariant 0 <= i <= |ops|
    invariant result + StackSimSpec(ops, stack, i) == StackSimSpec(ops, [], 0)
    decreases |ops| - i
  {
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
}
