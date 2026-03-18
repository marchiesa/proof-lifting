ghost function Abs(x: int): int
{
  if x >= 0 then x else -x
}

// True when some pair of elements in a differ by exactly 1
ghost predicate HasAdjacentPair(a: seq<int>)
{
  exists i, j | 0 <= i < |a| && 0 <= j < |a| && i != j :: Abs(a[i] - a[j]) == 1
}

// A valid team assignment: each student maps to a team in [0..numTeams),
// and no two students on the same team have skill values differing by 1.
ghost predicate ValidAssignment(a: seq<int>, assignment: seq<int>, numTeams: int)
{
  |assignment| == |a| &&
  numTeams >= 1 &&
  (forall i | 0 <= i < |a| :: 0 <= assignment[i] < numTeams) &&
  (forall i, j | 0 <= i < |a| && 0 <= j < |a| && i != j ::
    assignment[i] == assignment[j] ==> Abs(a[i] - a[j]) != 1)
}

// Constant sequence of length |a| — witness that 1 team suffices when no adjacent pair exists
ghost function ConstantSeq(a: seq<int>, v: int): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else ConstantSeq(a[..|a|-1], v) + [v]
}

// Parity-based assignment: team = a[i] % 2.
// If |a[i] - a[j]| = 1 then a[i] and a[j] have different parities,
// so they land on different teams. This witnesses 2-colorability.
ghost function ParityAssignment(a: seq<int>): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else ParityAssignment(a[..|a|-1]) + [a[|a|-1] % 2]
}

method YetAnotherDividingIntoTeams(a: seq<int>) returns (teams: int)
  // All programming skills are distinct and in [1, 100]
  requires forall i, j | 0 <= i < |a| && 0 <= j < |a| && i != j :: a[i] != a[j]
  requires forall i | 0 <= i < |a| :: 1 <= a[i] <= 100
  ensures teams == 1 || teams == 2
  // Feasibility: a valid partition into `teams` teams exists (constructive witness)
  ensures ValidAssignment(a, if teams == 1 then ConstantSeq(a, 0) else ParityAssignment(a), teams)
  // Minimality: 2 teams are needed iff there is a pair of students with adjacent skills
  ensures HasAdjacentPair(a) <==> teams == 2
{
  var b := new int[102];
  var i := 0;
  while i < 102 {
    b[i] := 0;
    i := i + 1;
  }
  i := 0;
  while i < |a| {
    if 0 <= a[i] < 102 {
      b[a[i]] := b[a[i]] + 1;
    }
    i := i + 1;
  }
  var flag := false;
  i := 1;
  while i <= 100 {
    if b[i] == 1 && (b[i + 1] == 1 || b[i - 1] == 1) {
      flag := true;
    }
    i := i + 1;
  }
  if flag {
    teams := 2;
  } else {
    teams := 1;
  }
}