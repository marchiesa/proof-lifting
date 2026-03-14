# Problem 5: Producer-Consumer Bounded Buffer State Machine

## Task
Simulate a producer-consumer system with a bounded buffer. A schedule (sequence of produce/consume operations) determines the order of operations. The producer feeds items from an input sequence into the buffer; the consumer drains items from the buffer into an output sequence. The spec requires: (1) output equals input (FIFO preserved), (2) buffer size never exceeds capacity, and (3) the schedule is valid.

## Why This Is Hard

1. **FIFO ordering proof**: Proving `output == input` requires showing that the buffer acts as a FIFO queue. Each item passes through the buffer in order, and the invariant must track that `output + buffer == input[..prodIdx]` at each step.

2. **Buffer bounds from counting argument**: The buffer size at each step equals `CountTrue(schedule[..step]) - CountFalse(schedule[..step])`. The invariant must relate the buffer size to prefix counts of the schedule, connecting imperative state to functional counting.

3. **Relating prefix counts to state**: The schedule validity predicate uses `CountTrue(schedule[..k])` which is a functional recursive definition. The invariant must maintain that `prodIdx == CountTrue(schedule[..step])` and `|output| == CountFalse(schedule[..step])`.

4. **Array safety**: Proving `buffer[0]` is safe requires showing the buffer is non-empty when consuming, which depends on the schedule prefix property. Proving `input[prodIdx]` is safe requires showing `prodIdx < |input|`.

5. **Sequence slicing and concatenation reasoning**: The key invariant `output + buffer == input[..prodIdx]` requires reasoning about how `+` and `[1..]` interact with sequence equality, which is notoriously tricky in Dafny.

6. **Ghost state for bufferSizes**: The `bufferSizes` sequence records history, adding another dimension to the invariant.

## Expected Invariants
- `prodIdx == CountTrue(schedule[..step])`
- `|output| == CountFalse(schedule[..step])`
- `output + buffer == input[..prodIdx]`
- `|buffer| == prodIdx - |output|`
- `|buffer| <= capacity` (from schedule precondition)
- `|bufferSizes| == step` and all recorded sizes are within bounds
