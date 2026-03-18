// Sum of a sequence of integers
ghost function SumSeq(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else SumSeq(s[..|s|-1]) + s[|s|-1]
}

// A valid dice face: the six-faced die has faces {2, 3, 4, 5, 6, 7}
ghost predicate ValidDiceFace(v: int)
{
  2 <= v <= 7
}

// Every element in the sequence is a valid dice face
ghost predicate AllValidFaces(dice: seq<int>)
{
  forall i | 0 <= i < |dice| :: ValidDiceFace(dice[i])
}

// Construct a concrete dice sequence achieving a target sum.
// Each die starts at minimum face value 2; the extra (target - 2*numRolls) is
// distributed greedily, adding up to 5 to each die (since max face is 7 = 2+5).
ghost function BuildDiceWitness(extra: int, numLeft: int): seq<int>
  requires numLeft >= 0
  decreases numLeft
{
  if numLeft == 0 then []
  else if numLeft == 1 then [2 + extra]
  else
    var add := if extra > 5 then 5 else if extra < 0 then 0 else extra;
    [2 + add] + BuildDiceWitness(extra - add, numLeft - 1)
}

// Build a witness dice sequence for the given target and number of rolls
ghost function DiceWitness(target: int, numRolls: int): seq<int>
  requires numRolls >= 1
{
  BuildDiceWitness(target - 2 * numRolls, numRolls)
}

// numRolls is a correct answer for target iff there exists a sequence of
// numRolls dice faces (each in {2..7}) whose sum equals target.
ghost predicate IsCorrectAnswer(target: int, numRolls: int)
{
  numRolls >= 1 &&
  exists dice: seq<int> :: |dice| == numRolls &&
    AllValidFaces(dice) &&
    SumSeq(dice) == target
}

method DiceRolling(x: seq<int>) returns (rolls: seq<int>)
  requires forall i | 0 <= i < |x| :: x[i] >= 2
  ensures |rolls| == |x|
  ensures forall i | 0 <= i < |rolls| :: IsCorrectAnswer(x[i], rolls[i])
{
  rolls := [];
  var i := 0;
  while i < |x|
  {
    var val := x[i];
    if val <= 7 {
      rolls := rolls + [1];
    } else {
      var r := val / 7;
      if val % 7 != 0 {
        r := r + 1;
      }
      rolls := rolls + [r];
    }
    i := i + 1;
  }
}