// Ghost variable probe: introduce sub-expressions as ghost vars but don't assert equality
ghost function TotalScore(student: seq<int>): int
  requires |student| >= 4
{
  student[0] + student[1] + student[2] + student[3]
}

ghost function CountBetter(students: seq<seq<int>>, threshold: int): int
  requires forall i | 0 <= i < |students| :: |students[i]| >= 4
  decreases |students|
{
  if |students| == 0 then 0
  else
    CountBetter(students[..|students|-1], threshold)
    + (if TotalScore(students[|students|-1]) > threshold then 1 else 0)
}

ghost function ExpectedRank(n: int, scores: seq<seq<int>>): int
  requires n >= 1
  requires |scores| >= n
  requires forall i | 0 <= i < n :: |scores[i]| >= 4
{
  1 + CountBetter(scores[1..n], TotalScore(scores[0]))
}

lemma CountBetterAppend(students: seq<seq<int>>, threshold: int, s: seq<int>)
  requires forall i | 0 <= i < |students| :: |students[i]| >= 4
  requires |s| >= 4
  ensures forall i | 0 <= i < |students + [s]| :: |(students + [s])[i]| >= 4
  ensures CountBetter(students + [s], threshold) == CountBetter(students, threshold) + (if TotalScore(s) > threshold then 1 else 0)
{
  var combined := students + [s];
  assert combined[..|combined|-1] == students;
}

method TheRank(n: int, scores: seq<seq<int>>) returns (rank: int)
  requires n >= 1
  requires |scores| >= n
  requires forall i | 0 <= i < n :: |scores[i]| >= 4
  ensures rank == ExpectedRank(n, scores)
{
  var myScore := scores[0][0] + scores[0][1] + scores[0][2] + scores[0][3];
  rank := 1;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant rank == 1 + CountBetter(scores[1..i], myScore)
  {
    var otherScore := scores[i][0] + scores[i][1] + scores[i][2] + scores[i][3];

    // Ghost variable probe: introduce terms but NO assert
    ghost var lhs := scores[1..i+1];
    ghost var rhs := scores[1..i] + [scores[i]];
    // NO assert lhs == rhs;

    CountBetterAppend(scores[1..i], myScore, scores[i]);

    if otherScore > myScore {
      rank := rank + 1;
    }
    i := i + 1;
  }
  assert scores[1..n] == scores[1..i];
  return;
}
