// ── Specification: Alexey and Train ──

// Input validity: formalizes the problem's constraints on inputs.
ghost predicate ValidInput(n: int, schedule: seq<(int, int)>, tm: seq<int>)
{
  n >= 1 &&
  |schedule| == n &&
  |tm| == n &&
  (forall i | 0 <= i < n :: schedule[i].0 < schedule[i].1) &&
  (forall i | 0 <= i < n :: tm[i] >= 0) &&
  (forall i | 1 <= i < n :: schedule[i - 1].1 < schedule[i].0)
}

// Ceiling of a / 2 for non-negative a.
ghost function CeilDiv2(a: int): int
{
  (a + 1) / 2
}

// The actual arrival time at the last station in the given schedule prefix.
// Models: the train travels exactly (a_i - b_{i-1} + tm_i) time from station i-1 to i,
// where b_0 = 0 (train departs terminal at time 0).
ghost function ArrivalTime(schedule: seq<(int, int)>, tm: seq<int>): int
  requires |schedule| > 0
  requires |tm| == |schedule|
  decreases |schedule|, 0
{
  var n := |schedule|;
  var prevB := if n == 1 then 0 else schedule[n - 2].1;
  var travelTime := schedule[n - 1].0 - prevB + tm[n - 1];
  if n == 1 then
    travelTime
  else
    DepartureTime(schedule[..n - 1], tm[..n - 1]) + travelTime
}

// The actual departure time from the last station in the given schedule prefix.
// Models the two departure conditions from the problem:
//   (1) the train has waited at least ceil((b_i - a_i) / 2) at station i, AND
//   (2) the current time is at least b_i.
// Therefore: departure_i = max(arrival_i + ceil((b_i - a_i) / 2), b_i).
ghost function DepartureTime(schedule: seq<(int, int)>, tm: seq<int>): int
  requires |schedule| > 0
  requires |tm| == |schedule|
  decreases |schedule|, 1
{
  var arrival := ArrivalTime(schedule, tm);
  var n := |schedule|;
  var ai := schedule[n - 1].0;
  var bi := schedule[n - 1].1;
  var minWait := CeilDiv2(bi - ai);
  var earliestDepart := arrival + minWait;
  if earliestDepart >= bi then earliestDepart else bi
}

// ── Implementation ──

method AlexeyAndTrain(n: int, schedule: seq<(int, int)>, tm: seq<int>) returns (arrivalTime: int)
  requires ValidInput(n, schedule, tm)
  ensures arrivalTime == ArrivalTime(schedule, tm)
{
  var currentTime := 0;
  var prevB := 0;
  var i := 0;
  while i < n
  {
    var ai := schedule[i].0;
    var bi := schedule[i].1;
    var travelTime := ai - prevB + tm[i];
    currentTime := currentTime + travelTime;
    if i < n - 1 {
      var waitTime := bi - ai;
      currentTime := currentTime + (waitTime + 1) / 2;
      if currentTime < bi {
        currentTime := bi;
      }
    }
    prevB := bi;
    i := i + 1;
  }
  arrivalTime := currentTime;
}