tags.

First, I need to look at the original code provided. The method PointsInSegments is supposed to return all points not covered by any segment, in strictly increasing order. The existing code has some invariants and ensures clauses, but maybe some assertions are missing where needed.

Looking at the first while loop where they process each segment. The invariant checks the relation between A and the segments processed so far. The inner loop marks the covered points as false in A. Then there's a forall loop that checks for each p whether A[p] is correctly updated. But maybe there's a missing assertion here.

Wait, in the first forall loop after processing a segment, the code checks if for each p, A[p] is equivalent to not being covered by any segment up to i+1. But maybe the code is missing an assertion that connects the A[p] after the inner loop to the segments processed. Let me check the code again.

In the first while loop, after the inner loop that marks A[j] as false, there's a forall loop over p. For each p, if it's in [a-1, b), then A[p] should be false. Otherwise, it should retain the previous value. Then, the code checks if for each p, A[p] is equivalent to not being in the current segment. But perhaps the code should have an assertion here to ensure that after processing the segment, the A array correctly reflects the coverage.

Wait, looking at the code:

    forall p | 0 <= p < m
      ensures A[p] <==> forall idx :: 0 <= idx < i + 1 ==> !PointInSegment(p + 1, segments[idx])
    {
      if a - 1 <= p < b {
        assert PointInSegment(p + 1, segments[i]);
      } else {
        assert !PointInSegment(p + 1, segments[i]);

      }
    }

Hmm, maybe the ensures clause here is part of a loop invariant. Wait, no, the forall here is a loop, but the code is using it as a loop to check the condition for each p. The ensures clause for the forall loop is that after processing, A[p] should be equivalent to not being covered by any segment up to i+1.

But perhaps the code is missing an assertion that after processing the current segment, the A array correctly reflects the coverage. Let me see. The code updates A for the current segment, but maybe the code needs to assert that after this update, the A array correctly represents the points not covered by any of the first i+1 segments.

Alternatively, maybe the code is missing an assertion in the outer loop's invariant that after processing all segments, A correctly represents the points not covered by any segment. Wait, the outer loop's invariant says:

    invariant forall p :: 0 <= p < m ==>
      (A[p] <==> forall idx :: 0 <= idx < i ==> !PointInSegment(p + 1, segments[idx]))

So after processing i segments, A[p] is true if p+1 is not covered by any of the first i segments. Then, after processing all segments (when i = |segments|), A[p] should be true if p+1 is not covered by any segment. Then, the code converts A into the result sequence.

But maybe the code is missing an assertion after the outer loop that checks that A correctly represents the points not covered by any segment. Let me look at the code after the outer loop:

  forall p | 0 <= p < m
    ensures A[p] <==> !PointCoveredByAny(p + 1, segments)
  {
  }

Wait, this is a loop that does nothing, but has an ensures clause. Maybe this is intended to be a ghost loop that checks the condition. But perhaps Dafny requires an assertion here. Wait, in Dafny, a loop with an ensures clause is a way to assert that after the loop, the condition holds. But if the loop body is empty, maybe it's a way to assert that the condition holds. However, maybe the code should have an assert statement instead.

Wait, the code after the outer loop has:

  forall p | 0 <= p < m
    ensures A[p] <==> !PointCoveredByAny(p + 1, segments)
  {
  }

But perhaps this is not sufficient. Maybe the code should have an assert statement here to ensure that after processing all segments, A[p] is correct. Alternatively, maybe the code should add an assertion in the outer loop's invariant that after the loop, A is correct.

Wait, the outer loop's invariant says that after processing i segments, A[p] is true if p+1 is not covered by any of the first i segments. When i reaches |segments|, then A[p] should be true if p+1 is not covered by any segment. So after the loop, the code should have:

assert forall p :: 0 <= p < m ==> A[p] <==> !PointCoveredByAny(p + 1, segments);

But maybe this assertion is missing. Let me check the code. The code does have a forall loop after the outer loop, but perhaps it's not sufficient. Maybe the code should add an assert statement here.

Wait, the code after the outer loop is:

  forall p | 0 <= p < m
    ensures A[p] <==> !PointCoveredByAny(p + 1, segments)
  {
  }

But this is a loop that does nothing. The ensures clause is part of the loop, so after the loop, Dafny should check that the condition holds. But maybe Dafny requires an explicit assert here. Alternatively, maybe the code should have an assert statement after this loop to ensure that the condition is met.

Alternatively, perhaps the code is missing an assertion in the inner loop that processes each segment. Let me look at the inner loop where they mark A[j] as false. The invariant here says that for p in [a-1, j), A[p] is false, and for others, it's the same as before. But maybe there's a missing assertion here.

Wait, in the inner loop:

    while j < b
      invariant a - 1 <= j <= b
      invariant |A| == m
      invariant forall p :: 0 <= p < m ==>
        if a - 1 <= p < j then A[p] == false
        else A[p] == A_before[p]
    {
      if 0 <= j < |A| {
        A := A[j := false];
      }
      j := j + 1;
    }

This loop marks A[j] as false for j from a-1 to b-1. The invariant ensures that after each step, the A array is correctly updated for the current j. But maybe the code is missing an assertion after this loop that connects the updated A to the segments processed.

Alternatively, the code might need to assert that after processing the current segment, the A array correctly reflects the coverage. For example, after processing segment i, for all p, A[p] is true if p+1 is not covered by any of the first i+1 segments.

Wait, the code after the inner loop has a forall loop:

    forall p | 0 <= p < m
      ensures A[p] <==> forall idx :: 0 <= idx < i + 1 ==> !PointInSegment(p + 1, segments[idx])
    {
      if a - 1 <= p < b {
        assert PointInSegment(p + 1, segments[i]);
      } else {
        assert !PointInSegment(p + 1, segments[i]);

      }
    }

This loop is intended to check that after processing segment i, A[p] is true if p+1 is not covered by any segment up to i+1. But maybe the code is missing an assertion here. For example, after the inner loop, the code should assert that for each p, A[p] is correctly updated.

Wait, the code inside the forall loop checks if p is in the current segment. If it is, then PointInSegment is true, else false. But maybe the code should also assert that A[p] is correctly set based on this. For example, if p is in the current segment, then A[p] should be false. Otherwise, it should retain the previous value. But the code already has the invariant from the inner loop. Hmm.

Alternatively, maybe the code is missing an assertion in the outer loop's invariant that after processing i segments, A correctly represents the points not covered by any of the first i segments. The current invariant says:

    invariant forall p :: 0 <= p < m ==>
      (A[p] <==> forall idx :: 0 <= idx < i ==> !PointInSegment(p + 1, segments[idx]))

But after processing segment i, the code should have the invariant for i+1. Wait, the outer loop is processing segments[i], and after processing, the code increments i. So during the iteration, the invariant is for segments up to i-1. Then, after processing segment i, the code should have the invariant for segments up to i. But maybe the code is missing an assertion here.

Wait, the code after processing segment i (inside the outer loop) has a forall loop that ensures that for each p, A[p] is equivalent to not being covered by any segment up to i+1. But maybe the code should have an assert statement here. For example:

assert forall p :: 0 <= p < m ==> A[p] <==> forall idx :: 0 <= idx < i + 1 ==> !PointInSegment(p + 1, segments[idx]);

But the code uses a forall loop with an ensures clause instead. Maybe Dafny requires explicit assertions here.

Alternatively, perhaps the code is missing an assertion in the final part where converting A to the result. Let me look at the code after the outer loop:

  forall p | 0 <= p < m
    ensures A[p] <==> !PointCoveredByAny(p + 1, segments)
  {
  }

  result := [];
  var k := 0;
  while k < m
    invariant 0 <= k <= m
    invariant |A| == m
    invariant forall p :: 0 <= p < m ==> (A[p] <==> !PointCoveredByAny(p + 1, segments))
    invariant forall q | 0 <= q < |result| :: 1 <= result[q] <= m
    invariant forall q | 0 <= q < |result| :: !PointCoveredByAny(result[q], segments)
    invariant forall p | 1 <= p <= k :: !PointCoveredByAny(p, segments) ==>
      exists q | 0 <= q < |result| :: result[q] == p
    invariant StrictlyIncreasing(result)
    invariant |result| > 0 ==> result[|result| - 1] <= k
  {
    ghost var old_result := result;
    if A[k] {
      // Inlined from StrictlyIncreasingAppend(result, k + 1)
      assert StrictlyIncreasing(result + [(k + 1)]);
      result := result + [k + 1];
    }

    k := k + 1;
  }

Here, the code has an invariant that for all p, A[p] is equivalent to not being covered by any segment. But maybe there's a missing assertion that after processing all segments, A correctly represents the uncovered points. The code does have the invariant, but maybe the code needs to explicitly assert that the result is built correctly.

Alternatively, maybe the code is missing an assertion in the final while loop that ensures that all uncovered points are added to the result. For example, when A[k] is true, adding k+1 to the result. But the code already has an invariant that if A[k] is true, then k+1 is not covered by any segment. So maybe the code is correct, but Dafny is not able to infer some steps.

Wait, the error message says that the code couldn't be extracted. Maybe the code has some syntax errors or missing parts. Let me check the code again.

Looking at the code, the first forall loop after the inner loop:

    forall p | 0 <= p < m
      ensures A[p] <==> forall idx :: 0 <= idx < i + 1 ==> !PointInSegment(p + 1, segments[idx])
    {
      if a - 1 <= p < b {
        assert PointInSegment(p + 1, segments[i]);
      } else {
        assert !PointInSegment(p + 1, segments[i]);

      }
    }

But there's a missing closing brace here. Wait, the code for the else clause has an assert, but the code block for the else is missing a closing brace. Let me check:

      if a - 1 <= p < b {
        assert PointInSegment(p + 1, segments[i]);
      } else {
        assert !PointInSegment(p + 1, segments[i]);

      }

Wait, the else block has two lines: the assert and a blank line. But in Dafny, each statement needs to be properly indented. Maybe the code is missing a closing brace here. Wait, no, the code uses braces for the if and else blocks. But in Dafny, the code can use either braces or indentation. But perhaps the code is written with braces. Let me check the code again.

Wait, the code for the if-else inside the forall loop is:

      if a - 1 <= p < b {
        assert PointInSegment(p + 1, segments[i]);
      } else {
        assert !PointInSegment(p + 1, segments[i]);

      }

But the else block has the assert statement and then a blank line. But in Dafny, the else block is properly bracketed. So that's correct. So the code should be okay.

Another possible issue is that the code uses 'ensures' in the forall loop, but Dafny might require that the loop body actually does something. But the loop body here is just the if-else with asserts. Wait, but the code is a loop over p, and for each p, it's checking the condition and asserting. But the loop is not modifying any variables. So maybe the code should be written as a ghost loop with ensures clauses, but perhaps Dafny requires that the ensures clause is provable.

Alternatively, maybe the code is missing an assertion after the outer loop that connects A to the segments. Let me add an assertion after the outer loop:

assert forall p :: 0 <= p < m ==> A[p] <==> !PointCoveredByAny(p + 1, segments);

This would ensure that after processing all segments, A correctly represents the uncovered points. Then, the code can build the result based on A.

Another possible issue is in the final while loop where building the result. The code has an invariant that for all p up to k, if p is uncovered, then it's in the result. But maybe there's a missing assertion here. For example, when A[k] is true, adding k+1 to the result. The code already checks that the result remains strictly increasing, but maybe there's a missing assertion that the new result is still strictly increasing.

Wait, the code has:

      assert StrictlyIncreasing(result + [(k + 1)]);

Which is correct. So the code should be okay.

Putting it all together, the code might need an assertion after the outer loop to ensure that A correctly represents the uncovered points. Let me modify the code to add that assertion.

So, after the outer loop:

  }

  // After processing all segments, A correctly represents uncovered points
  assert forall p :: 0 <= p < m ==> A[p] <==> !PointCoveredByAny(p + 1, segments);

  forall p | 0 <= p < m
    ensures A[p] <==> !PointCoveredByAny(p + 1, segments)
  {
  }

But wait, the code already has the forall loop after the outer loop. Maybe adding an explicit assert here would help.

So modifying the code to add an assert after the outer loop:

  assert forall p :: 0 <= p < m ==> A[p] <==> !PointCoveredByAny(p + 1, segments);

This would explicitly check that after processing all segments, A is correct.

Another possible place is in the inner loop where marking A[j] as false. The code has an invariant that for p in [a-1, j), A[p] is false. But maybe the code should also assert that for j >= b, all p in [a-1, b) are false.

But the inner loop runs until j reaches b. So after the loop, the invariant would have j = b, so for p in [a-1, b), A[p] is false. So the code should be correct.

Another possible issue is in the first forall loop after processing the segment. The code checks if for each p, A[p] is correctly updated. But maybe the code should have an assertion that after this loop, the condition holds. For example:

    assert forall p :: 0 <= p < m ==> A[p] <==> forall idx :: 0 <= idx < i + 1 ==> !PointInSegment(p + 1, segments[idx]);

But the code already has the ensures clause in the forall loop. Maybe adding an explicit assert here would help.

So, modifying the code inside the outer loop:

    forall p | 0 <= p < m
      ensures A[p] <==> forall idx :: 0 <= idx < i + 1 ==> !PointInSegment(p + 1, segments[idx])
    {
      if a - 1 <= p < b {
        assert PointInSegment(p + 1, segments[i]);
      } else {
        assert !PointInSegment(p + 1, segments[i]);
      }
    }

    // Ensure that after processing segment i, A is correctly updated
    assert forall p :: 0 <= p < m ==> A[p] <==> forall idx :: 0 <= idx < i + 1 ==> !PointInSegment(p + 1, segments[idx]);

But this might be redundant, but perhaps necessary for Dafny to verify.

Alternatively, maybe the code is missing an assertion in the final part where building the result. For example, when adding k+1 to the result, the code should assert that k+1 is not covered by any segment. But the code already has the invariant that if A[k] is true, then k+1 is not covered. So the code should be okay.

Putting all this together, the code might need to add the following assertions:

1. After the outer loop, assert that A correctly represents the uncovered points.
2. After the forall loop that checks the segments, add an assert to ensure the condition holds.

So modifying the code:

After the outer loop:

  }

  // Assert that after processing all segments, A is correct
  assert forall p :: 0 <= p < m ==> A[p] <==> !PointCoveredByAny(p + 1, segments);

  forall p | 0 <= p < m
    ensures A[p] <==> !PointCoveredByAny(p + 1, segments)
  {
  }

But wait, the code already has the forall loop after the outer loop. Maybe adding the assert before the forall loop would help.

Alternatively, maybe the code should remove the forall loop and replace it with an assert. For example:

  assert forall p :: 0 <= p < m ==> A[p] <==> !PointCoveredByAny(p + 1, segments);

But the code uses a forall loop with an empty body and an ensures clause. Maybe Dafny requires that the loop body is executed, but in this case, the loop is empty. So perhaps replacing the loop with an assert would be better.

So modifying the code:

  // After processing all segments, ensure A correctly represents uncovered points
  assert forall p :: 0 <= p < m ==> A[p] <==> !PointCoveredByAny(p + 1, segments);

Then, remove the following loop:

  forall p | 0 <= p < m
    ensures A[p] <==> !PointCoveredByAny(p + 1, segments)
  {
  }

But wait, the code might need this loop to establish the ensures clause. Alternatively, maybe the code can be simplified by removing the loop and adding the assert.

But I'm not sure. Let me check the original code again.

The original code after the outer loop has:

  forall p | 0 <= p < m
    ensures A[p] <==> !PointCoveredByAny(p + 1, segments)
  {
  }

This is a loop that does nothing but has an ensures clause. The purpose is to assert that after the loop, the condition holds. But maybe Dafny requires that the loop body is executed, but in this case, the loop runs zero times. So perhaps the code should be replaced with an explicit assert.

So modifying the code to:

  assert forall p :: 0 <= p < m ==> A[p] <==> !PointCoveredByAny(p + 1, segments);

But in Dafny, an assert statement is used to check a condition. So this would add the necessary assertion.

Another possible place is in the first forall loop after processing a segment. The code has:

    forall p | 0 <= p < m
      ensures A[p] <==> forall idx :: 0 <= idx < i + 1 ==> !PointInSegment(p + 1, segments[idx])
    {
      if a - 1 <= p < b {
        assert PointInSegment(p + 1, segments[i]);
      } else {
        assert !PointInSegment(p + 1, segments[i]);
      }
    }

But maybe after this loop, the code should assert that the condition holds. So adding:

    assert forall p :: 0 <= p < m ==> A[p] <==> forall idx :: 0 <= idx < i + 1 ==> !PointInSegment(p + 1, segments[idx]);

But the ensures clause of the loop should already establish this. However, maybe Dafny is not able to infer this, so adding the explicit assert would help.

Putting all this together, the code might need the following changes:

1. After the first forall loop inside the outer loop, add an assert to check the condition.
2. After the outer loop, add an assert to check that A correctly represents uncovered points.

So modifying the code:

Inside the outer loop:

    forall p | 0 <= p < m
      ensures A[p] <==> forall idx :: 0 <= idx < i + 1 ==> !PointInSegment(p + 1, segments[idx])
    {
      if a - 1 <= p < b {
        assert PointInSegment(p + 1, segments[i]);
      } else {
        assert !PointInSegment(p + 1, segments[i]);
      }
    }

    // Ensure that after processing segment i, A is correctly updated
    assert forall p :: 0 <= p < m ==> A[p] <==> forall idx :: 0 <= idx < i + 1 ==> !PointInSegment(p + 1, segments[idx]);

After the outer loop:

  }

  // Assert that after processing all segments, A correctly represents uncovered points
  assert forall p :: 0 <= p < m ==> A[p] <==> !PointCoveredByAny(p + 1, segments);

  // Remove the empty forall loop
  // forall p | 0 <= p < m
  //   ensures A[p] <==> !PointCoveredByAny(p + 1, segments)
  // {
  // }

But wait, the code after the outer loop is:

  forall p | 0 <= p < m
    ensures A[p] <==> !PointCoveredByAny(p + 1, segments)
  {
  }

Which is a loop that does nothing. If we replace this with an assert, then the code would have:

  assert forall p :: 0 <= p < m ==> A[p] <==> !PointCoveredByAny(p + 1, segments);

But the code already has the invariant in the final while loop that A[p] is correct. So maybe the code is missing an assertion here.

Putting all these changes together, the code would look like this:

```dafny
ghost predicate PointInSegment(p: int, seg: (int, int))
{
  seg.0 <= p <= seg.1
}

ghost predicate PointCoveredByAny(p: int, segments: seq<(int, int)>)
{
  exists i | 0 <= i < |segments| :: PointInSegment(p, segments[i])
}

ghost predicate StrictlyIncreasing(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] < s[j]
}

method PointsInSegments(segments: seq<(int, int)>, m: int) returns (result: seq<int>)
  requires m >= 0
  requires forall i | 0 <= i < |segments| :: 1 <= segments[i].0 <= segments[i].1 <= m
  // Every output point is a valid point in [1, m] that is not covered by any segment
  ensures forall i | 0 <= i < |result| :: 1 <= result[i] <= m
  ensures forall i | 0 <= i < |result| :: !PointCoveredByAny(result[i], segments)
  // Every uncovered point in [1, m] appears in the result (completeness)
  ensures forall p | 1 <= p <= m :: !PointCoveredByAny(p, segments) ==>
    (exists j | 0 <= j < |result| :: result[j] == p)
  // Output is in strictly increasing order (implies no duplicates)
  ensures StrictlyIncreasing(result)
{
  var A := seq(m, (_: int) => true);
  var i := 0;
  while i < |segments|
    invariant 0 <= i <= |segments|
    invariant |A| == m
    invariant forall p :: 0 <= p < m ==>
      (A[p] <==> forall idx :: 0 <= idx < i ==> !PointInSegment(p + 1, segments[idx]))
  {
    var a := segments[i].0;
    var b := segments[i].1;
    ghost var A_before := A;
    var j := a - 1;
    while j < b
      invariant a - 1 <= j <= b
      invariant |A| == m
      invariant forall p :: 0 <= p < m ==>
        if a - 1 <= p < j then A[p] == false
        else A[p] == A_before[p]
    {
      if 0 <= j < |A| {
        A := A[j := false];
      }
      j := j + 1;
    }

    forall p | 0 <= p < m
      ensures A[p] <==> forall idx :: 0 <= idx < i + 1 ==> !PointInSegment(p + 1, segments[idx])
    {
      if a - 1 <= p < b {
        assert PointInSegment(p + 1, segments[i]);
      } else {
        assert !PointInSegment(p + 1, segments[i]);
      }
    }

    // Ensure that after processing segment i, A is correctly updated
    assert forall p :: 0 <= p < m ==> A[p] <==> forall idx :: 0 <= idx < i + 1 ==> !PointInSegment(p + 1, segments[idx]);

    i := i + 1;
  }

  // After processing all segments, ensure A correctly represents uncovered points
  assert forall p :: 0 <= p < m ==> A[p] <==> !PointCoveredByAny(p + 1, segments);

  result := [];
  var k := 0;
  while k < m
    invariant 0 <= k <= m
    invariant |A| == m
    invariant forall p :: 0 <= p < m ==> (A[p] <==> !PointCoveredByAny(p + 1, segments))
    invariant forall q | 0 <= q < |result| :: 1 <= result[q] <= m
    invariant forall q | 0 <= q < |result| :: !PointCoveredByAny(result[q], segments)
    invariant forall p | 1 <= p <= k :: !PointCoveredByAny(p, segments) ==>
      exists q | 0 <= q < |result| :: result[q] == p
    invariant StrictlyIncreasing(result)
    invariant |result| > 0 ==> result[|result| - 1] <= k
  {
    ghost var old_result := result;
    if A[k] {
      // Inlined from StrictlyIncreasingAppend(result, k + 1)
      assert StrictlyIncreasing(result + [(k + 1)]);
      result := result + [k + 1];
    }

    k := k + 1;
  }
}
```

This adds two assertions:

1. After processing each segment, assert that A correctly represents points not covered by the first i+1 segments.
2. After processing all segments, assert that A correctly represents points not covered by any segment.

These assertions should help Dafny verify the correctness of the code.
◁/think▷

<DAFNY_CODE>
ghost predicate PointInSegment(p: int, seg: (int, int))
{
  seg.0 <= p <= seg.1
}

ghost predicate PointCoveredByAny(p: int, segments: seq<(int, int)>)
{
  exists i | 0 <= i < |segments| :: PointInSegment(p, segments[i])
}

ghost predicate StrictlyIncreasing(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] < s[j]
}

method PointsInSegments(segments: seq<(int, int)>, m: int) returns (result: seq<int>)
  requires m >= 0
  requires forall i | 0 <= i < |segments| :: 1 <= segments[i].0 <= segments[i].1 <= m
  // Every output point is a valid point in [1, m] that is not covered by any segment
  ensures forall i | 0 <= i < |result| :: 1 <= result[i] <= m
  ensures forall i | 0 <= i < |result| :: !PointCoveredByAny(result[i], segments)
  // Every uncovered point in [1, m] appears in the result (completeness)
  ensures forall p | 1 <= p <= m :: !PointCoveredByAny(p, segments) ==>
    (exists j | 0 <= j < |result| :: result[j] == p)
  // Output is in strictly increasing order (implies no duplicates)
  ensures StrictlyIncreasing(result)
{
  var A := seq(m, (_: int) => true);
  var i := 0;
  while i < |segments|
    invariant 0 <= i <= |segments|
    invariant |A| == m
    invariant forall p :: 0 <= p < m ==>
      (A[p] <==> forall idx :: 0 <= idx < i ==> !PointInSegment(p + 1, segments[idx]))
  {
    var a := segments[i].0;
    var b := segments[i].1;
    ghost var A_before := A;
    var j := a - 1;
    while j < b
      invariant a - 1 <= j <= b
      invariant |A| == m
      invariant forall p :: 0 <= p < m ==>
        if a - 1 <= p < j then A[p] == false
        else A[p] == A_before[p]
    {
      if 0 <= j < |A| {
        A := A[j := false];
      }
      j := j + 1;
    }

    forall p | 0 <= p < m
      ensures A[p] <==> forall idx :: 0 <= idx < i + 1 ==> !PointInSegment(p + 1, segments[idx])
    {
      if a - 1 <= p < b {
        assert PointInSegment(p + 1, segments[i]);
      } else {
        assert !PointInSegment(p + 1, segments[i]);
      }
    }

    // Ensure that after processing segment i, A is correctly updated
    assert forall p :: 0 <= p < m ==> A[p] <==> forall idx :: 0 <= idx < i + 1 ==> !PointInSegment(p + 1, segments[idx]);

    i := i + 1;
  }

  // After processing all segments, ensure A correctly represents uncovered points
  assert forall p :: 0 <= p < m ==> A[p] <==> !PointCoveredByAny(p + 1, segments);

  result := [];
  var k := 0;
  while k < m
    invariant 0 <= k <= m
    invariant |A| == m
    invariant forall p :: 0 <= p < m ==> (A[p] <==> !PointCoveredByAny(p + 1, segments))
    invariant forall q | 0 <= q < |result| :: 1 <= result[q] <= m
    invariant forall q | 0 <= q < |result| :: !PointCoveredByAny(result[q], segments)
    invariant forall p | 1 <= p <= k :: !PointCoveredByAny(p, segments) ==>
      exists q | 0 <= q < |result| :: result[q] == p
    invariant StrictlyIncreasing(result)
    invariant |result| > 0 ==> result[|result| - 1] <= k
  {
    ghost var old_result := result;
    if A[k] {
      // Inlined from StrictlyIncreasingAppend(result, k + 1)
      assert StrictlyIncreasing(result + [(k + 1)]);
      result := result + [k + 1];
    }

    k := k + 1;
  }
}