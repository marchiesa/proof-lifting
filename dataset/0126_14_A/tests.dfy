predicate Rectangular(grid: seq<string>)
{
  |grid| > 0 &&
  forall i | 0 <= i < |grid| :: |grid[i]| == |grid[0]|
}

predicate HasStar(grid: seq<string>)
{
  exists r | 0 <= r < |grid| ::
    exists c | 0 <= c < |grid[r]| ::
      grid[r][c] == '*'
}

predicate IsSubRectangle(grid: seq<string>, result: seq<string>,
                         top: int, bottom: int, left: int, right: int)
{
  0 <= top < bottom <= |grid| &&
  0 <= left < right &&
  (forall r | top <= r < bottom :: right <= |grid[r]|) &&
  |result| == bottom - top &&
  (forall i | 0 <= i < bottom - top :: result[i] == grid[top + i][left..right])
}

predicate ContainsAllShaded(grid: seq<string>,
                            top: int, bottom: int, left: int, right: int)
{
  forall r | 0 <= r < |grid| ::
    forall c | 0 <= c < |grid[r]| ::
      grid[r][c] == '*' ==> (top <= r < bottom && left <= c < right)
}

predicate TightBounds(grid: seq<string>,
                      top: int, bottom: int, left: int, right: int)
{
  0 <= top < bottom <= |grid| &&
  0 <= left < right &&
  (forall r | top <= r < bottom :: right <= |grid[r]|) &&
  (exists c | left <= c < right :: grid[top][c] == '*') &&
  (exists c | left <= c < right :: grid[bottom - 1][c] == '*') &&
  (exists r | top <= r < bottom :: grid[r][left] == '*') &&
  (exists r | top <= r < bottom :: grid[r][right - 1] == '*')
}

predicate IsMinimalBoundingBox(grid: seq<string>, result: seq<string>,
                               top: int, bottom: int, left: int, right: int)
{
  IsSubRectangle(grid, result, top, bottom, left, right) &&
  ContainsAllShaded(grid, top, bottom, left, right) &&
  TightBounds(grid, top, bottom, left, right)
}

// Wrapper predicate matching the ensures clause of Letter
predicate SatisfiesSpec(grid: seq<string>, result: seq<string>)
{
  |grid| > 0 &&
  exists top | 0 <= top < |grid| ::
    exists bottom | 0 <= bottom <= |grid| ::
      exists left | 0 <= left < |grid[0]| ::
        exists right | 0 <= right <= |grid[0]| ::
          IsMinimalBoundingBox(grid, result, top, bottom, left, right)
}

method Letter(grid: seq<string>) returns (result: seq<string>)
  decreases *
  requires Rectangular(grid)
  requires HasStar(grid)
  ensures exists top | 0 <= top < |grid| ::
            exists bottom | 0 <= bottom <= |grid| ::
              exists left | 0 <= left < |grid[0]| ::
                exists right | 0 <= right <= |grid[0]| ::
                  IsMinimalBoundingBox(grid, result, top, bottom, left, right)
{
  var lines := grid;

  while true
    decreases *
  {
    if |lines| == 0 { break; }

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
  // ===== SPEC POSITIVE TESTS =====
  // Testing SatisfiesSpec (the top-level ensures predicate) with correct outputs.
  // Skipping pairs 1 (6x7) and 10 (15x3) — too large for bounded quantifier enumeration.

  expect SatisfiesSpec(["***", "*.*", "***"], ["***", "*.*", "***"]), "spec positive 2";
  expect SatisfiesSpec(["*"], ["*"]), "spec positive 3";
  expect SatisfiesSpec(["*", "*"], ["*", "*"]), "spec positive 4";
  expect SatisfiesSpec([".", "*", ".", ".", "."], ["*"]), "spec positive 5";
  expect SatisfiesSpec(["*****."], ["*****"]), "spec positive 6";
  expect SatisfiesSpec(["..", "*."], ["*"]), "spec positive 7";
  expect SatisfiesSpec(["..*.", "....", "...."], ["*"]), "spec positive 8";
  expect SatisfiesSpec(["..", "..", "..", "..", "..", "*.", "..", ".."], ["*"]), "spec positive 9";

  // ===== SPEC NEGATIVE TESTS =====
  // Testing SatisfiesSpec rejects wrong outputs (each has " WRONG" appended to last line).
  // Skipping pairs 1 (6x7) and 10 (15x3) — too large for bounded quantifier enumeration.

  expect !SatisfiesSpec(["***", "*.*", "***"], ["***", "*.*", "*** WRONG"]), "spec negative 2";
  expect !SatisfiesSpec(["*"], ["* WRONG"]), "spec negative 3";
  expect !SatisfiesSpec(["*", "*"], ["*", "* WRONG"]), "spec negative 4";
  expect !SatisfiesSpec([".", "*", ".", ".", "."], ["* WRONG"]), "spec negative 5";
  expect !SatisfiesSpec(["*****."], ["***** WRONG"]), "spec negative 6";
  expect !SatisfiesSpec(["..", "*."], ["* WRONG"]), "spec negative 7";
  expect !SatisfiesSpec(["..*.", "....", "...."], ["* WRONG"]), "spec negative 8";
  expect !SatisfiesSpec(["..", "..", "..", "..", "..", "*.", "..", ".."], ["* WRONG"]), "spec negative 9";

  // ===== IMPLEMENTATION TESTS =====
  var r: seq<string>;

  r := Letter([".......", "..***..","..*...." ,"..***..","..*...." ,"..***.."]);
  expect r == ["***", "*..", "***", "*..", "***"], "impl test 1 failed";

  r := Letter(["***", "*.*", "***"]);
  expect r == ["***", "*.*", "***"], "impl test 2 failed";

  r := Letter(["*"]);
  expect r == ["*"], "impl test 3 failed";

  r := Letter(["*", "*"]);
  expect r == ["*", "*"], "impl test 4 failed";

  r := Letter([".", "*", ".", ".", "."]);
  expect r == ["*"], "impl test 5 failed";

  r := Letter(["*****."]); 
  expect r == ["*****"], "impl test 6 failed";

  r := Letter(["..", "*."]);
  expect r == ["*"], "impl test 7 failed";

  r := Letter(["..*.", "....", "...."]);
  expect r == ["*"], "impl test 8 failed";

  r := Letter(["..", "..", "..", "..", "..", "*.", "..", ".."]);
  expect r == ["*"], "impl test 9 failed";

  r := Letter(["...", "...", "...", ".**", "...", "...", "*..", "...", ".*.", "..*", "..*", "*..", "..*", "...", "..."]);
  expect r == [".**", "...", "...", "*..", "...", ".*.", "..*", "..*", "*..", "..*"], "impl test 10 failed";

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
  ], "impl test 11 failed";

  r := Letter(["..................*.*............................."]);
  expect r == ["*.*"], "impl test 12 failed";

  r := Letter(["*", "."]);
  expect r == ["*"], "impl test 13 failed";

  r := Letter(["*", "*", "*", "*", "*"]);
  expect r == ["*", "*", "*", "*", "*"], "impl test 14 failed";

  r := Letter(["**......"]);
  expect r == ["**"], "impl test 15 failed";

  r := Letter(["*.", ".."]);
  expect r == ["*"], "impl test 16 failed";

  r := Letter(["...*", "*...", "..*."] );
  expect r == ["...*", "*...", "..*."], "impl test 17 failed";

  r := Letter(["**", "**", "**", "**", "**", "**", "**", "**"]);
  expect r == ["**", "**", "**", "**", "**", "**", "**", "**"], "impl test 18 failed";

  r := Letter(["***", "***", "***", "***", "***", "***", "*..", "...", "...", ".*.", "...", ".**", ".*.", "...", "..."]);
  expect r == ["***", "***", "***", "***", "***", "***", "*..", "...", "...", ".*.", "...", ".**", ".*."], "impl test 19 failed";

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
  ], "impl test 20 failed";

  print "All tests passed\n";
}