/*
 * Problem 5: Producer-Consumer Bounded Buffer State Machine
 */

ghost predicate ValidSchedule(schedule: seq<bool>, numItems: int)
{
  CountTrue(schedule) == numItems &&
  CountFalse(schedule) == numItems &&
  (forall k :: 0 <= k <= |schedule| ==>
    CountTrue(schedule[..k]) >= CountFalse(schedule[..k]))
}

function CountTrue(s: seq<bool>): int
{
  if |s| == 0 then 0
  else (if s[0] then 1 else 0) + CountTrue(s[1..])
}

function CountFalse(s: seq<bool>): int
{
  if |s| == 0 then 0
  else (if !s[0] then 1 else 0) + CountFalse(s[1..])
}

ghost predicate ProducerConsumerSpec(
  input: seq<int>,
  schedule: seq<bool>,
  capacity: int,
  output: seq<int>,
  bufferSizes: seq<int>
)
  requires capacity >= 1
{
  ValidSchedule(schedule, |input|) &&
  output == input &&
  |bufferSizes| == |schedule| &&
  (forall k :: 0 <= k < |bufferSizes| ==> 0 <= bufferSizes[k] <= capacity)
}

// Lemma: CountTrue(s[..n+1]) = CountTrue(s[..n]) + (if s[n] then 1 else 0)
lemma CountTrueStep(s: seq<bool>, n: int)
  requires 0 <= n < |s|
  ensures CountTrue(s[..n+1]) == CountTrue(s[..n]) + (if s[n] then 1 else 0)
  decreases n
{
  if n == 0 {
    assert s[..1] == [s[0]];
    assert s[..0] == [];
  } else {
    assert s[..n+1] == [s[0]] + s[1..n+1];
    assert s[..n] == [s[0]] + s[1..n];
    // CountTrue([s[0]] + rest) = (if s[0] then 1 else 0) + CountTrue(rest)
    assert ([s[0]] + s[1..n+1])[0] == s[0];
    assert ([s[0]] + s[1..n+1])[1..] == s[1..n+1];
    assert ([s[0]] + s[1..n])[0] == s[0];
    assert ([s[0]] + s[1..n])[1..] == s[1..n];
    // So CountTrue(s[..n+1]) = (if s[0] ...) + CountTrue(s[1..n+1])
    // And CountTrue(s[..n]) = (if s[0] ...) + CountTrue(s[1..n])
    // By induction on s[1..]: CountTrue(s[1..][..n]) = CountTrue(s[1..][..n-1]) + ...
    assert s[1..n+1] == s[1..][..n];
    assert s[1..n] == s[1..][..n-1];
    assert s[1..][n-1] == s[n];
    CountTrueStep(s[1..], n-1);
  }
}

lemma CountFalseStep(s: seq<bool>, n: int)
  requires 0 <= n < |s|
  ensures CountFalse(s[..n+1]) == CountFalse(s[..n]) + (if !s[n] then 1 else 0)
  decreases n
{
  if n == 0 {
    assert s[..1] == [s[0]];
    assert s[..0] == [];
  } else {
    assert s[..n+1] == [s[0]] + s[1..n+1];
    assert s[..n] == [s[0]] + s[1..n];
    assert ([s[0]] + s[1..n+1])[0] == s[0];
    assert ([s[0]] + s[1..n+1])[1..] == s[1..n+1];
    assert ([s[0]] + s[1..n])[0] == s[0];
    assert ([s[0]] + s[1..n])[1..] == s[1..n];
    assert s[1..n+1] == s[1..][..n];
    assert s[1..n] == s[1..][..n-1];
    assert s[1..][n-1] == s[n];
    CountFalseStep(s[1..], n-1);
  }
}

// CountTrue + CountFalse == |s|
lemma CountTruePlusFalse(s: seq<bool>)
  ensures CountTrue(s) + CountFalse(s) == |s|
{
  if |s| > 0 {
    CountTruePlusFalse(s[1..]);
  }
}

// CountTrue(s) == CountTrue(s[..n]) + CountTrue(s[n..])
lemma CountTrueSplit(s: seq<bool>, n: int)
  requires 0 <= n <= |s|
  ensures CountTrue(s) == CountTrue(s[..n]) + CountTrue(s[n..])
  decreases n
{
  if n == 0 {
    assert s[..0] == [];
    assert s[0..] == s;
  } else {
    assert s[..n] == [s[0]] + s[1..n];
    assert s[1..n] == s[1..][..n-1];
    assert s[n..] == s[1..][n-1..];
    CountTrueSplit(s[1..], n-1);
    assert CountTrue(s[1..]) == CountTrue(s[1..][..n-1]) + CountTrue(s[1..][n-1..]);
    assert CountTrue(s) == (if s[0] then 1 else 0) + CountTrue(s[1..]);
    assert ([s[0]] + s[1..n])[0] == s[0];
    assert ([s[0]] + s[1..n])[1..] == s[1..n];
    assert CountTrue(s[..n]) == (if s[0] then 1 else 0) + CountTrue(s[1..n]);
  }
}

lemma CountTrueFirstTrue(s: seq<bool>)
  requires |s| > 0
  requires s[0] == true
  ensures CountTrue(s) >= 1
{
  CountTrueNonNeg(s[1..]);
  assert CountTrue(s) == 1 + CountTrue(s[1..]);
}

lemma CountTrueNonNeg(s: seq<bool>)
  ensures CountTrue(s) >= 0
{
  if |s| > 0 {
    CountTrueNonNeg(s[1..]);
  }
}

method SimulateProducerConsumer(input: seq<int>, schedule: seq<bool>, capacity: int)
  returns (output: seq<int>, bufferSizes: seq<int>)
  requires capacity >= 1
  requires ValidSchedule(schedule, |input|)
  requires forall k :: 0 <= k <= |schedule| ==>
    CountTrue(schedule[..k]) - CountFalse(schedule[..k]) <= capacity
  ensures ProducerConsumerSpec(input, schedule, capacity, output, bufferSizes)
{
  var buffer: seq<int> := [];
  output := [];
  bufferSizes := [];
  var prodIdx := 0;
  var consIdx := 0;

  assert schedule[..0] == [];

  var step := 0;
  while step < |schedule|
    invariant 0 <= step <= |schedule|
    invariant |bufferSizes| == step
    invariant prodIdx == CountTrue(schedule[..step])
    invariant consIdx == CountFalse(schedule[..step])
    invariant 0 <= consIdx <= prodIdx <= |input|
    invariant buffer == input[consIdx..prodIdx]
    invariant output == input[..consIdx]
    invariant |buffer| == prodIdx - consIdx
    invariant forall k :: 0 <= k < step ==> 0 <= bufferSizes[k] <= capacity
  {
    CountTrueStep(schedule, step);
    CountFalseStep(schedule, step);

    if schedule[step] {
      // Produce
      // prodIdx < |input| because CountTrue hasn't reached its final value
      assert CountTrue(schedule[..step]) < CountTrue(schedule) by {
        CountTrueSplit(schedule, step);
        assert CountTrue(schedule) == CountTrue(schedule[..step]) + CountTrue(schedule[step..]);
        assert schedule[step..][0] == schedule[step] == true;
        CountTrueFirstTrue(schedule[step..]);
        assert CountTrue(schedule[step..]) >= 1;
      }
      assert prodIdx < |input|;
      buffer := buffer + [input[prodIdx]];
      prodIdx := prodIdx + 1;
      assert buffer == input[consIdx..prodIdx] by {
        assert input[consIdx..prodIdx] == input[consIdx..prodIdx-1] + [input[prodIdx-1]];
      }
    } else {
      // Consume
      // Buffer is non-empty because produces > consumes at this point
      assert |buffer| > 0 by {
        // schedule[step] is false, so:
        // CountTrue(schedule[..step+1]) == CountTrue(schedule[..step])
        // CountFalse(schedule[..step+1]) == CountFalse(schedule[..step]) + 1
        // ValidSchedule requires CountTrue(schedule[..step+1]) >= CountFalse(schedule[..step+1])
        // So CountTrue(schedule[..step]) >= CountFalse(schedule[..step]) + 1
        // i.e., prodIdx > consIdx, i.e., |buffer| > 0
        assert CountTrue(schedule[..step+1]) == CountTrue(schedule[..step]);
        assert CountFalse(schedule[..step+1]) == CountFalse(schedule[..step]) + 1;
      }
      assert buffer[0] == input[consIdx];
      output := output + [buffer[0]];
      buffer := buffer[1..];
      consIdx := consIdx + 1;
      assert output == input[..consIdx] by {
        assert input[..consIdx] == input[..consIdx-1] + [input[consIdx-1]];
      }
    }

    // Buffer size within capacity
    assert |buffer| <= capacity by {
      // |buffer| == CountTrue(schedule[..step+1]) - CountFalse(schedule[..step+1])
      // By precondition with k == step+1: this is <= capacity
      assert CountTrue(schedule[..step+1]) - CountFalse(schedule[..step+1]) <= capacity;
    }

    bufferSizes := bufferSizes + [|buffer|];
    step := step + 1;
  }

  assert schedule[..|schedule|] == schedule;
  assert prodIdx == CountTrue(schedule) == |input|;
  assert consIdx == CountFalse(schedule) == |input|;
  assert output == input[..|input|] == input;
}
