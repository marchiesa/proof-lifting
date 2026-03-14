/*
 * Tests for Problem 5: Producer-Consumer Bounded Buffer
 *
 * We test the spec predicates on concrete schedules and inputs.
 */

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

ghost predicate ValidSchedule(schedule: seq<bool>, numItems: int)
{
  CountTrue(schedule) == numItems &&
  CountFalse(schedule) == numItems &&
  (forall k :: 0 <= k <= |schedule| ==>
    CountTrue(schedule[..k]) >= CountFalse(schedule[..k]))
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

// Helper lemmas for CountTrue/CountFalse
lemma CountTrueFalseEmpty()
  ensures CountTrue([]) == 0
  ensures CountFalse([]) == 0
{}

lemma CountBool1(b: bool)
  ensures CountTrue([b]) == (if b then 1 else 0)
  ensures CountFalse([b]) == (if !b then 1 else 0)
{
  assert [b][1..] == [];
}

lemma CountBool2(a: bool, b: bool)
  ensures CountTrue([a, b]) == (if a then 1 else 0) + (if b then 1 else 0)
  ensures CountFalse([a, b]) == (if !a then 1 else 0) + (if !b then 1 else 0)
{
  assert [a, b][1..] == [b];
  CountBool1(b);
}

lemma CountBool4(a: bool, b: bool, c: bool, d: bool)
  ensures CountTrue([a,b,c,d]) == (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) + (if d then 1 else 0)
  ensures CountFalse([a,b,c,d]) == (if !a then 1 else 0) + (if !b then 1 else 0) + (if !c then 1 else 0) + (if !d then 1 else 0)
{
  assert [a,b,c,d][1..] == [b,c,d];
  assert [b,c,d][1..] == [c,d];
  CountBool2(c, d);
}

// Test 1: Empty input, empty schedule
method test1()
{
  var input: seq<int> := [];
  var schedule: seq<bool> := [];
  var output: seq<int> := [];
  var bufferSizes: seq<int> := [];

  // ValidSchedule: CountTrue([]) == 0, CountFalse([]) == 0
  assert CountTrue(schedule) == 0;
  assert CountFalse(schedule) == 0;

  // Prefix check: only k=0, schedule[..0] = []
  assert schedule[..0] == [];
  assert ValidSchedule(schedule, 0);
  assert ProducerConsumerSpec(input, schedule, 1, output, bufferSizes);
}

// Test 2: input=[42], schedule=[true, false] (produce then consume), capacity=1
method test2()
{
  var input := [42];
  var schedule := [true, false];
  var output := [42];
  var bufferSizes := [1, 0];

  CountBool2(true, false);
  assert CountTrue(schedule) == 1;
  assert CountFalse(schedule) == 1;

  // Prefix checks
  assert schedule[..0] == [];
  assert schedule[..1] == [true];
  assert schedule[..2] == [true, false];
  CountBool1(true);
  CountBool2(true, false);

  assert CountTrue(schedule[..0]) == 0;
  assert CountFalse(schedule[..0]) == 0;
  assert CountTrue(schedule[..1]) == 1;
  assert CountFalse(schedule[..1]) == 0;
  assert CountTrue(schedule[..2]) == 1;
  assert CountFalse(schedule[..2]) == 1;

  assert ValidSchedule(schedule, 1);
  assert output == input;
  assert |bufferSizes| == |schedule|;
  assert bufferSizes[0] == 1 <= 1;
  assert bufferSizes[1] == 0 <= 1;
  assert ProducerConsumerSpec(input, schedule, 1, output, bufferSizes);
}

// Test 3: input=[1,2], schedule=[true,true,false,false], capacity=2
// Produce both, then consume both
method test3()
{
  var input := [1, 2];
  var schedule := [true, true, false, false];
  var output := [1, 2];
  var bufferSizes := [1, 2, 1, 0];

  CountBool4(true, true, false, false);
  assert CountTrue(schedule) == 2;
  assert CountFalse(schedule) == 2;

  // Prefix checks
  assert schedule[..0] == [];
  assert schedule[..1] == [true];
  assert schedule[..2] == [true, true];
  assert schedule[..3] == [true, true, false];
  assert schedule[..4] == schedule;

  CountBool1(true);
  CountBool2(true, true);

  assert [true, true, false][1..] == [true, false];
  CountBool2(true, false);

  assert CountTrue(schedule[..0]) == 0 >= 0 == CountFalse(schedule[..0]);
  assert CountTrue(schedule[..1]) == 1 >= 0 == CountFalse(schedule[..1]);
  assert CountTrue(schedule[..2]) == 2 >= 0 == CountFalse(schedule[..2]);
  assert CountTrue(schedule[..3]) == 2 >= 1 == CountFalse(schedule[..3]);
  assert CountTrue(schedule[..4]) == 2 >= 2 == CountFalse(schedule[..4]);

  assert ValidSchedule(schedule, 2);
  assert output == input;
  assert |bufferSizes| == |schedule|;
  assert ProducerConsumerSpec(input, schedule, 2, output, bufferSizes);
}

// Test 4: input=[10,20], schedule=[true,false,true,false], capacity=1
// Interleaved: produce, consume, produce, consume
method test4()
{
  var input := [10, 20];
  var schedule := [true, false, true, false];
  var output := [10, 20];
  var bufferSizes := [1, 0, 1, 0];

  CountBool4(true, false, true, false);
  assert CountTrue(schedule) == 2;
  assert CountFalse(schedule) == 2;

  assert schedule[..0] == [];
  assert schedule[..1] == [true];
  assert schedule[..2] == [true, false];
  assert schedule[..3] == [true, false, true];
  assert schedule[..4] == schedule;

  CountBool1(true);
  CountBool2(true, false);

  assert [true, false, true][1..] == [false, true];
  CountBool2(false, true);

  assert CountTrue(schedule[..0]) >= CountFalse(schedule[..0]);
  assert CountTrue(schedule[..1]) >= CountFalse(schedule[..1]);
  assert CountTrue(schedule[..2]) >= CountFalse(schedule[..2]);
  assert CountTrue(schedule[..3]) >= CountFalse(schedule[..3]);
  assert CountTrue(schedule[..4]) >= CountFalse(schedule[..4]);

  assert ValidSchedule(schedule, 2);
  assert output == input;
  assert ProducerConsumerSpec(input, schedule, 1, output, bufferSizes);
}
