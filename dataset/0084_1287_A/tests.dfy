predicate ValidState(s: seq<char>)
{
  forall i | 0 <= i < |s| :: s[i] == 'A' || s[i] == 'P'
}

function OneStep(s: seq<char>): seq<char>
{
  seq(|s|, j requires 0 <= j < |s| =>
    if s[j] == 'A' || (j > 0 && s[j-1] == 'A' && s[j] == 'P') then 'A' else s[j])
}

function Simulate(s: seq<char>, steps: nat): seq<char>
  decreases steps
{
  if steps == 0 then s else Simulate(OneStep(s), steps - 1)
}

predicate IsFixedPoint(s: seq<char>)
{
  OneStep(s) == s
}

// Combined top-level spec predicate from the ensures clauses
predicate AngryStudentsSpec(s: string, steps: int)
{
  ValidState(s) &&
  steps >= 0 &&
  IsFixedPoint(Simulate(s, steps)) &&
  (forall k: int | 0 <= k < steps :: !IsFixedPoint(Simulate(s, k)))
}

method {:verify false} AngryStudents(s: string) returns (steps: int)
  decreases *
  requires ValidState(s)
  ensures steps >= 0
  ensures IsFixedPoint(Simulate(s, steps))
  ensures forall k: int | 0 <= k < steps :: !IsFixedPoint(Simulate(s, k))
{
  var n := |s|;
  var line := new char[n];
  var i := 0;
  while i < n {
    line[i] := s[i];
    i := i + 1;
  }

  steps := 0;
  while true
    decreases *
  {
    var flag := false;
    var j := n - 1;
    while j >= 0 {
      if line[j] == 'A' && j + 1 < n && line[j + 1] == 'P' {
        line[j + 1] := 'A';
        flag := true;
      }
      j := j - 1;
    }
    if !flag {
      break;
    }
    steps := steps + 1;
  }
}

method {:verify false} Main()
  decreases *
{
  var r: int;

  // === SPEC POSITIVE TESTS ===
  // Small inputs where spec holds for correct answer
  expect AngryStudentsSpec("A", 0), "spec positive 1";
  expect AngryStudentsSpec("P", 0), "spec positive 2";
  expect AngryStudentsSpec("AP", 1), "spec positive 3";
  expect AngryStudentsSpec("PA", 0), "spec positive 4";
  expect AngryStudentsSpec("AAP", 1), "spec positive 5";
  expect AngryStudentsSpec("PPA", 0), "spec positive 6";

  // === SPEC NEGATIVE TESTS ===
  // Spec must reject wrong answers
  expect !AngryStudentsSpec("PPAP", 2), "spec negative 1";  // correct 1, wrong 2 (from Neg 1)
  expect !AngryStudentsSpec("AAP", 2), "spec negative 2";   // correct 1, wrong 2 (scaled from Neg 2)
  expect !AngryStudentsSpec("A", 1), "spec negative 3";     // correct 0, wrong 1 (from Neg 3)
  expect !AngryStudentsSpec("PPPP", 1), "spec negative 4";  // correct 0, wrong 1 (from Neg 4)
  expect !AngryStudentsSpec("AP", 2), "spec negative 5";    // correct 1, wrong 2 (scaled from Neg 5)

  // === IMPLEMENTATION TESTS ===
  // Test 1
  r := AngryStudents("PPAP");
  expect r == 1, "impl test 1";

  // Test 2
  r := AngryStudents("APPAPPPAPPPP");
  expect r == 4, "impl test 2a";
  r := AngryStudents("AAP");
  expect r == 1, "impl test 2b";
  r := AngryStudents("PPA");
  expect r == 0, "impl test 2c";

  // Test 3
  r := AngryStudents("A");
  expect r == 0, "impl test 3a";
  r := AngryStudents("P");
  expect r == 0, "impl test 3b";
  r := AngryStudents("AP");
  expect r == 1, "impl test 3c";
  r := AngryStudents("PA");
  expect r == 0, "impl test 3d";
  r := AngryStudents("PPPPAPPP");
  expect r == 3, "impl test 3e";
  r := AngryStudents("PPPPPPPA");
  expect r == 0, "impl test 3f";
  r := AngryStudents("APPPPPPP");
  expect r == 7, "impl test 3g";
  r := AngryStudents("PPPPPPAP");
  expect r == 1, "impl test 3h";
  r := AngryStudents("PPPPPAPP");
  expect r == 2, "impl test 3i";
  r := AngryStudents("PPPAPPPP");
  expect r == 4, "impl test 3j";

  // Test 4
  r := AngryStudents("PPPP");
  expect r == 0, "impl test 4a";
  r := AngryStudents("APPP");
  expect r == 3, "impl test 4b";
  r := AngryStudents("PAPP");
  expect r == 2, "impl test 4c";
  r := AngryStudents("AAPP");
  expect r == 2, "impl test 4d";
  r := AngryStudents("PPAP");
  expect r == 1, "impl test 4e";
  r := AngryStudents("APAP");
  expect r == 1, "impl test 4f";
  r := AngryStudents("PAAP");
  expect r == 1, "impl test 4g";
  r := AngryStudents("AAAP");
  expect r == 1, "impl test 4h";
  r := AngryStudents("PPPA");
  expect r == 0, "impl test 4i";
  r := AngryStudents("APPA");
  expect r == 2, "impl test 4j";
  r := AngryStudents("PAPA");
  expect r == 1, "impl test 4k";
  r := AngryStudents("AAPA");
  expect r == 1, "impl test 4l";
  r := AngryStudents("PPAA");
  expect r == 0, "impl test 4m";
  r := AngryStudents("APAA");
  expect r == 1, "impl test 4n";
  r := AngryStudents("PAAA");
  expect r == 0, "impl test 4o";
  r := AngryStudents("AAAA");
  expect r == 0, "impl test 4p";

  // Test 5
  r := AngryStudents("PAPPPAPAAPAAPAAPPAAAPPAPPAPAAAAPPAPPAPPPAAAAAAPPAAAPAAAAAPAPAPAAAAPPAPAAAAPPAPPPPPAAAAAAAPAAAAPAPPAP");
  expect r == 5, "impl test 5";

  print "All tests passed\n";
}