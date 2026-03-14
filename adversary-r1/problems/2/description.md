# Problem 2: Multi-Loop Pipeline — Frequency Filter Reconstruction

## Task
Given a sequence of integers and a threshold k, produce the subsequence containing only elements that appear at least k times in the input, preserving order. The implementation uses a 4-loop pipeline: build frequency map, extract keys, filter frequent elements, reconstruct output.

## Why This Is Hard

1. **Four sequential loops with carried state**: Each loop produces data consumed by the next. The prover must discover invariants for each loop that are strong enough to establish the next loop's precondition.

2. **Map-to-set-to-sequence reasoning**: Loop 1 builds a `map<int, int>`, loop 2-3 convert map information to a `set<int>`, loop 4 uses the set to filter. The invariants must bridge these different data structure representations.

3. **Existential witness in the spec**: The postcondition uses `exists indices: seq<int>` to express the order-preserving filter property. The prover must construct this witness and show it satisfies all six conjuncts simultaneously.

4. **CountOccurrences linking**: The frequency map built imperatively must be shown equivalent to the recursive `CountOccurrences` function used in the spec. This requires a loop invariant relating `freq[v]` to `CountOccurrences(input[..i], v)` for all v.

5. **Non-deterministic set iteration**: The loop that converts `freq.Keys` to a sequence uses a `:|` (such-that) operator, meaning the key order is non-deterministic. The invariant must handle arbitrary orderings.

## Expected Invariants
- Loop 1: `forall v :: v in freq <==> CountOccurrences(input[..i], v) > 0` and `freq[v] == CountOccurrences(input[..i], v)`
- Loop 2: remaining subset tracking
- Loop 3: `frequentSet` contains exactly the keys with count >= k processed so far
- Loop 4: `output` and `indices` track the filtered subsequence with all witness properties
