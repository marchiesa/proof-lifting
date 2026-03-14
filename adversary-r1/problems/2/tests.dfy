/*
 * Tests for Problem 2: Frequency Filter Reconstruction
 *
 * We test the spec predicates on known input-output pairs.
 */

function CountOccurrences(s: seq<int>, v: int): int
  ensures CountOccurrences(s, v) >= 0
{
  if |s| == 0 then 0
  else (if s[0] == v then 1 else 0) + CountOccurrences(s[1..], v)
}

ghost predicate IsOrderPreservingFilter(input: seq<int>, output: seq<int>, k: int)
  requires k >= 1
{
  exists indices: seq<int> ::
    |indices| == |output| &&
    (forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |input|) &&
    (forall i :: 0 <= i < |indices| ==> input[indices[i]] == output[i]) &&
    (forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j]) &&
    (forall i :: 0 <= i < |input| && CountOccurrences(input, input[i]) >= k ==>
      i in indices) &&
    (forall i :: 0 <= i < |output| ==> CountOccurrences(input, output[i]) >= k)
}

ghost predicate FreqFilterSpec(input: seq<int>, k: int, output: seq<int>)
  requires k >= 1
{
  IsOrderPreservingFilter(input, output, k)
}

lemma CountOccEmpty(v: int)
  ensures CountOccurrences([], v) == 0
{}

lemma CountOccSingleton(a: int, v: int)
  ensures CountOccurrences([a], v) == (if a == v then 1 else 0)
{
  assert [a][1..] == [];
}

lemma CountOccPair(a: int, b: int, v: int)
  ensures CountOccurrences([a, b], v) == (if a == v then 1 else 0) + (if b == v then 1 else 0)
{
  assert [a, b][1..] == [b];
  CountOccSingleton(b, v);
}

lemma CountOcc3(a: int, b: int, c: int, v: int)
  ensures CountOccurrences([a, b, c], v) == (if a == v then 1 else 0) + (if b == v then 1 else 0) + (if c == v then 1 else 0)
{
  assert [a, b, c][1..] == [b, c];
  CountOccPair(b, c, v);
}

lemma CountOcc4(a: int, b: int, c: int, d: int, v: int)
  ensures CountOccurrences([a, b, c, d], v) == (if a == v then 1 else 0) + (if b == v then 1 else 0) + (if c == v then 1 else 0) + (if d == v then 1 else 0)
{
  assert [a, b, c, d][1..] == [b, c, d];
  CountOcc3(b, c, d, v);
}

lemma CountOcc5(a: int, b: int, c: int, d: int, e: int, v: int)
  ensures CountOccurrences([a, b, c, d, e], v) == (if a == v then 1 else 0) + (if b == v then 1 else 0) + (if c == v then 1 else 0) + (if d == v then 1 else 0) + (if e == v then 1 else 0)
{
  assert [a, b, c, d, e][1..] == [b, c, d, e];
  CountOcc4(b, c, d, e, v);
}

// Test 1: Empty input -> empty output
method test1()
{
  var input: seq<int> := [];
  var output: seq<int> := [];
  var indices: seq<int> := [];

  assert |indices| == |output|;
  assert IsOrderPreservingFilter(input, output, 1);
  assert FreqFilterSpec(input, 1, output);
}

// Test 2: [1,2,1,3,1] with k=2 -> [1,1,1] (only 1 appears >= 2 times)
method test2()
{
  var input := [1, 2, 1, 3, 1];
  var output := [1, 1, 1];

  CountOcc5(1, 2, 1, 3, 1, 1);
  CountOcc5(1, 2, 1, 3, 1, 2);
  CountOcc5(1, 2, 1, 3, 1, 3);
  assert CountOccurrences(input, 1) == 3;
  assert CountOccurrences(input, 2) == 1;
  assert CountOccurrences(input, 3) == 1;

  // The witness indices are [0, 2, 4]
  var indices := [0, 2, 4];
  assert |indices| == |output| == 3;
  assert input[0] == output[0] == 1;
  assert input[2] == output[1] == 1;
  assert input[4] == output[2] == 1;
  assert indices[0] < indices[1] < indices[2];

  assert 0 in indices;
  assert 2 in indices;
  assert 4 in indices;

  // input[1]=2 has count 1 < 2, not in indices - OK
  // input[3]=3 has count 1 < 2, not in indices - OK

  assert IsOrderPreservingFilter(input, output, 2);
  assert FreqFilterSpec(input, 2, output);
}

// Test 3: [1,2,1,2] with k=2 -> [1,2,1,2] (all elements appear >= 2 times)
method test3()
{
  var input := [1, 2, 1, 2];
  var output := [1, 2, 1, 2];

  var indices := [0, 1, 2, 3];
  assert |indices| == |output| == 4;
  assert input[0] == output[0];
  assert input[1] == output[1];
  assert input[2] == output[2];
  assert input[3] == output[3];

  assert 0 in indices;
  assert 1 in indices;
  assert 2 in indices;
  assert 3 in indices;

  CountOcc4(1, 2, 1, 2, 1);
  CountOcc4(1, 2, 1, 2, 2);
  assert CountOccurrences(input, 1) == 2;
  assert CountOccurrences(input, 2) == 2;

  assert IsOrderPreservingFilter(input, output, 2);
  assert FreqFilterSpec(input, 2, output);
}

// Test 4: [5,5,5] with k=3 -> [5,5,5]
method test4()
{
  var input := [5, 5, 5];
  var output := [5, 5, 5];
  var indices := [0, 1, 2];

  CountOcc3(5, 5, 5, 5);
  assert CountOccurrences(input, 5) == 3;

  assert 0 in indices && 1 in indices && 2 in indices;
  assert input[0] == output[0];
  assert input[1] == output[1];
  assert input[2] == output[2];

  assert IsOrderPreservingFilter(input, output, 3);
  assert FreqFilterSpec(input, 3, output);
}
