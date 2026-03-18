method Letter(grid: seq<string>) returns (result: seq<string>)
  decreases *
{
  var lines := grid;

  while true
    decreases *
  {
    if |lines| == 0 { break; }

    // Check if any line starts with '*'
    var a := false;
    var i := 0;
    while i < |lines|
      decreases |lines| - i
    {
      if |lines[i]| > 0 && lines[i][0] == '*' {
        a := true;
        break;
      }
      i := i + 1;
    }
    if !a {
      var newLines: seq<string> := [];
      i := 0;
      while i < |lines|
        decreases |lines| - i
      {
        if |lines[i]| > 0 {
          newLines := newLines + [lines[i][1..]];
        }
        i := i + 1;
      }
      lines := newLines;
      continue;
    }

    // Check if any line ends with '*'
    var b := false;
    i := 0;
    while i < |lines|
      decreases |lines| - i
    {
      if |lines[i]| > 0 && lines[i][|lines[i]| - 1] == '*' {
        b := true;
        break;
      }
      i := i + 1;
    }
    if !b {
      var newLines: seq<string> := [];
      i := 0;
      while i < |lines|
        decreases |lines| - i
      {
        if |lines[i]| > 0 {
          newLines := newLines + [lines[i][..|lines[i]| - 1]];
        }
        i := i + 1;
      }
      lines := newLines;
      continue;
    }

    // Check if first row is all dots
    var allDots := true;
    var j := 0;
    while j < |lines[0]|
      decreases |lines[0]| - j
    {
      if lines[0][j] != '.' {
        allDots := false;
        break;
      }
      j := j + 1;
    }
    if allDots {
      lines := lines[1..];
      continue;
    }

    // Check if last row is all dots
    allDots := true;
    j := 0;
    while j < |lines[|lines| - 1]|
      decreases |lines[|lines| - 1]| - j
    {
      if lines[|lines| - 1][j] != '.' {
        allDots := false;
        break;
      }
      j := j + 1;
    }
    if allDots {
      lines := lines[..|lines| - 1];
      continue;
    }

    break;
  }

  result := lines;
}

method Main()
  decreases *
{
  // Test 1
  var r := Letter([".......", "..***..","..*...." ,"..***..","..*...." ,"..***.."]);
  expect r == ["***", "*..", "***", "*..", "***"], "Test 1 failed";

  // Test 2
  r := Letter(["***", "*.*", "***"]);
  expect r == ["***", "*.*", "***"], "Test 2 failed";

  // Test 3
  r := Letter(["*"]);
  expect r == ["*"], "Test 3 failed";

  // Test 4
  r := Letter(["*", "*"]);
  expect r == ["*", "*"], "Test 4 failed";

  // Test 5
  r := Letter([".", "*", ".", ".", "."]);
  expect r == ["*"], "Test 5 failed";

  // Test 6
  r := Letter(["*****."]);
  expect r == ["*****"], "Test 6 failed";

  // Test 7
  r := Letter(["..", "*."]);
  expect r == ["*"], "Test 7 failed";

  // Test 8
  r := Letter(["..*.", "....", "...."]);
  expect r == ["*"], "Test 8 failed";

  // Test 9
  r := Letter(["..", "..", "..", "..", "..", "*.", "..", ".."]);
  expect r == ["*"], "Test 9 failed";

  // Test 10
  r := Letter(["...", "...", "...", ".**", "...", "...", "*..", "...", ".*.", "..*", "..*", "*..", "..*", "...", "..."]);
  expect r == [".**", "...", "...", "*..", "...", ".*.", "..*", "..*", "*..", "..*"], "Test 10 failed";

  // Test 11
  r := Letter([
    ".", ".", ".", ".", ".", ".", ".", ".", ".", ".",
    ".", ".", ".", ".", ".", "*", ".", "*", ".", ".",
    ".", ".", ".", ".", ".", ".", ".", ".", ".", ".",
    ".", ".", ".", ".", ".", "*", ".", ".", ".", ".",
    ".", ".", ".", ".", ".", ".", ".", ".", ".", "."
  ]);
  expect r == [
    "*", ".", "*", ".", ".", ".", ".", ".", ".", ".",
    ".", ".", ".", ".", ".", ".", ".", ".", ".", ".",
    "*"
  ], "Test 11 failed";

  // Test 12
  r := Letter(["..................*.*............................."]);
  expect r == ["*.*"], "Test 12 failed";

  // Test 13
  r := Letter(["*", "."]);
  expect r == ["*"], "Test 13 failed";

  // Test 14
  r := Letter(["*", "*", "*", "*", "*"]);
  expect r == ["*", "*", "*", "*", "*"], "Test 14 failed";

  // Test 15
  r := Letter(["**......"]);
  expect r == ["**"], "Test 15 failed";

  // Test 16
  r := Letter(["*.", ".."]);
  expect r == ["*"], "Test 16 failed";

  // Test 17
  r := Letter(["...*", "*...", "..*."] );
  expect r == ["...*", "*...", "..*."], "Test 17 failed";

  // Test 18
  r := Letter(["**", "**", "**", "**", "**", "**", "**", "**"]);
  expect r == ["**", "**", "**", "**", "**", "**", "**", "**"], "Test 18 failed";

  // Test 19
  r := Letter(["***", "***", "***", "***", "***", "***", "*..", "...", "...", ".*.", "...", ".**", ".*.", "...", "..."]);
  expect r == ["***", "***", "***", "***", "***", "***", "*..", "...", "...", ".*.", "...", ".**", ".*."], "Test 19 failed";

  // Test 20
  r := Letter([
    ".", "*", "*", "*", ".", ".", "*", ".", "*", "*",
    "*", "*", "*", "*", "*", ".", "*", "*", "*", "*",
    "*", "*", "*", "*", "*", "*", "*", "*", "*", ".",
    ".", ".", ".", "*", "*", ".", "*", "*", ".", ".",
    ".", ".", "*", "*", ".", ".", ".", ".", ".", "."
  ]);
  expect r == [
    "*", "*", "*", ".", ".", "*", ".", "*", "*", "*",
    "*", "*", "*", "*", ".", "*", "*", "*", "*", "*",
    "*", "*", "*", "*", "*", "*", "*", "*", ".", ".",
    ".", ".", "*", "*", ".", "*", "*", ".", ".", ".",
    ".", "*", "*"
  ], "Test 20 failed";

  print "All tests passed\n";
}