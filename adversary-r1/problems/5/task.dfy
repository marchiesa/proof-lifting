/*
 * Problem 5: Producer-Consumer Bounded Buffer State Machine
 *
 * Simulate a producer-consumer system with a bounded buffer.
 * The producer generates items from a sequence, the consumer processes them.
 * Operations are interleaved according to a schedule.
 *
 * The spec says: after processing the full schedule, the consumer's
 * output sequence equals the producer's input sequence (FIFO ordering
 * preserved), the buffer never exceeds capacity, and all items are consumed.
 */

// Schedule entry: true = produce, false = consume
// A valid schedule must produce each item exactly once and consume each exactly once

ghost predicate ValidSchedule(schedule: seq<bool>, numItems: int)
{
  // Number of produce operations equals numItems
  CountTrue(schedule) == numItems &&
  // Number of consume operations equals numItems
  CountFalse(schedule) == numItems &&
  // At every prefix, #produces >= #consumes (can't consume from empty buffer)
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

// The full spec
ghost predicate ProducerConsumerSpec(
  input: seq<int>,
  schedule: seq<bool>,
  capacity: int,
  output: seq<int>,
  bufferSizes: seq<int>  // buffer size at each step for the capacity check
)
  requires capacity >= 1
{
  // Schedule is valid
  ValidSchedule(schedule, |input|) &&
  // Output equals input (FIFO preserved)
  output == input &&
  // Buffer never exceeds capacity
  |bufferSizes| == |schedule| &&
  (forall k :: 0 <= k < |bufferSizes| ==> 0 <= bufferSizes[k] <= capacity)
}

method SimulateProducerConsumer(input: seq<int>, schedule: seq<bool>, capacity: int)
  returns (output: seq<int>, bufferSizes: seq<int>)
  requires capacity >= 1
  requires ValidSchedule(schedule, |input|)
  // Buffer never exceeds capacity at any step
  requires forall k :: 0 <= k <= |schedule| ==>
    CountTrue(schedule[..k]) - CountFalse(schedule[..k]) <= capacity
  ensures ProducerConsumerSpec(input, schedule, capacity, output, bufferSizes)
{
  var buffer: seq<int> := [];
  output := [];
  bufferSizes := [];
  var prodIdx := 0;  // next item to produce
  var consIdx := 0;  // for tracking (not used in logic)

  var step := 0;
  while step < |schedule|
    // INVARIANT NEEDED HERE
  {
    if schedule[step] {
      // Produce: add input[prodIdx] to buffer
      buffer := buffer + [input[prodIdx]];
      prodIdx := prodIdx + 1;
    } else {
      // Consume: remove from front of buffer, add to output
      output := output + [buffer[0]];
      buffer := buffer[1..];
    }
    bufferSizes := bufferSizes + [|buffer|];
    step := step + 1;
  }
}
