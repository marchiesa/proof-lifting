method {:verify false} AngryStudents(s: string) returns (steps: int)
  decreases *
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

  // Test 1
  r := AngryStudents("PPAP");
  expect r == 1, "PPAP";

  // Test 2
  r := AngryStudents("APPAPPPAPPPP");
  expect r == 4, "APPAPPPAPPPP";
  r := AngryStudents("AAP");
  expect r == 1, "AAP";
  r := AngryStudents("PPA");
  expect r == 0, "PPA";

  // Test 3
  r := AngryStudents("A");
  expect r == 0, "A";
  r := AngryStudents("P");
  expect r == 0, "P";
  r := AngryStudents("AP");
  expect r == 1, "AP";
  r := AngryStudents("PA");
  expect r == 0, "PA";
  r := AngryStudents("PPPPAPPP");
  expect r == 3, "PPPPAPPP";
  r := AngryStudents("PPPPPPPA");
  expect r == 0, "PPPPPPPA";
  r := AngryStudents("APPPPPPP");
  expect r == 7, "APPPPPPP";
  r := AngryStudents("PPPPPPAP");
  expect r == 1, "PPPPPPAP";
  r := AngryStudents("PPPPPAPP");
  expect r == 2, "PPPPPAPP";
  r := AngryStudents("PPPAPPPP");
  expect r == 4, "PPPAPPPP";

  // Test 4
  r := AngryStudents("PPPP");
  expect r == 0, "PPPP";
  r := AngryStudents("APPP");
  expect r == 3, "APPP";
  r := AngryStudents("PAPP");
  expect r == 2, "PAPP";
  r := AngryStudents("AAPP");
  expect r == 2, "AAPP";
  r := AngryStudents("PPAP");
  expect r == 1, "PPAP 2";
  r := AngryStudents("APAP");
  expect r == 1, "APAP";
  r := AngryStudents("PAAP");
  expect r == 1, "PAAP";
  r := AngryStudents("AAAP");
  expect r == 1, "AAAP";
  r := AngryStudents("PPPA");
  expect r == 0, "PPPA";
  r := AngryStudents("APPA");
  expect r == 2, "APPA";
  r := AngryStudents("PAPA");
  expect r == 1, "PAPA";
  r := AngryStudents("AAPA");
  expect r == 1, "AAPA";
  r := AngryStudents("PPAA");
  expect r == 0, "PPAA";
  r := AngryStudents("APAA");
  expect r == 1, "APAA";
  r := AngryStudents("PAAA");
  expect r == 0, "PAAA";
  r := AngryStudents("AAAA");
  expect r == 0, "AAAA";

  // Test 5
  r := AngryStudents("PAPPPAPAAPAAPAAPPAAAPPAPPAPAAAAPPAPPAPPPAAAAAAPPAAAPAAAAAPAPAPAAAAPPAPAAAAPPAPPPPPAAAAAAAPAAAAPAPPAP");
  expect r == 5, "long string";

  print "All tests passed\n";
}