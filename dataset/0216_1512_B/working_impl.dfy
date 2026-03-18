method AlmostRectangle(n: int, grid: seq<seq<char>>) returns (result: seq<seq<char>>)
{
  var res := new seq<char>[n];
  var i := 0;
  while i < n {
    res[i] := grid[i];
    i := i + 1;
  }

  var a := -1;
  var c := -1;
  var b := -1;
  var d := -1;
  i := 0;
  while i < n {
    var j := 0;
    while j < |res[i]| {
      if res[i][j] == '*' {
        if a == -1 {
          a := i;
          c := j;
        } else {
          b := i;
          d := j;
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }

  if a != b && c != d {
    res[a] := res[a][d := '*'];
    res[b] := res[b][c := '*'];
  } else if a == b {
    var nr := 0;
    if nr == a {
      nr := 1;
    }
    res[nr] := res[nr][c := '*'];
    res[nr] := res[nr][d := '*'];
  } else {
    var nc := 0;
    if nc == c {
      nc := 1;
    }
    res[a] := res[a][nc := '*'];
    res[b] := res[b][nc := '*'];
  }

  result := [];
  i := 0;
  while i < n {
    result := result + [res[i]];
    i := i + 1;
  }
}

method Main()
{
  // Test 1a
  var r := AlmostRectangle(4, ["..*.","....","*...","...."]);
  expect r == ["*.*.","....","*.*.","...."], "Test 1a failed";

  // Test 1b
  r := AlmostRectangle(2, ["*.",".*"]);
  expect r == ["**","**"], "Test 1b failed";

  // Test 1c
  r := AlmostRectangle(2, [".*",".*"]);
  expect r == ["**","**"], "Test 1c failed";

  // Test 1d
  r := AlmostRectangle(3, ["*.*","...","..."]);
  expect r == ["*.*","*.*","..."], "Test 1d failed";

  // Test 1e
  r := AlmostRectangle(5, [".....","..*..",".....",".*...","....."]); 
  expect r == [".....",".**..",".....",".**..","....."], "Test 1e failed";

  // Test 1f
  r := AlmostRectangle(4, ["....","....","*...","*..."]);
  expect r == ["....","....","**..","**.."], "Test 1f failed";

  // Test 2
  r := AlmostRectangle(2, ["*.",".*"]);
  expect r == ["**","**"], "Test 2 failed";

  // Test 3
  r := AlmostRectangle(2, ["*.","*."]);
  expect r == ["**","**"], "Test 3 failed";

  // Test 4
  r := AlmostRectangle(3, ["*..","...","..*"]);
  expect r == ["*.*","...","*.*"], "Test 4 failed";

  // Test 5
  r := AlmostRectangle(3, [".*.",".*.",  "..."]);
  expect r == ["**.","**.","..."], "Test 5 failed";

  // Test 6
  r := AlmostRectangle(4, ["*...","....","....","...*"]);
  expect r == ["*..*","....","....","*..*"], "Test 6 failed";

  // Test 7
  r := AlmostRectangle(2, ["**",".."]);
  expect r == ["**","**"], "Test 7 failed";

  // Test 8
  r := AlmostRectangle(3, ["...","*.*","..."]);
  expect r == ["*.*","*.*","..."], "Test 8 failed";

  // Test 9
  r := AlmostRectangle(5, [".....",".*...",".....","...*.","....."]); 
  expect r == [".....",".*.*.",".....",".*.*.","....."], "Test 9 failed";

  // Test 10a
  r := AlmostRectangle(2, ["*.",".*"]);
  expect r == ["**","**"], "Test 10a failed";

  // Test 10b
  r := AlmostRectangle(2, [".*",".*"]);
  expect r == ["**","**"], "Test 10b failed";

  // Test 11a
  r := AlmostRectangle(2, ["**",".."]);
  expect r == ["**","**"], "Test 11a failed";

  // Test 11b
  r := AlmostRectangle(3, ["*..","*..","..."]);
  expect r == ["**.","**.","..."], "Test 11b failed";

  // Test 11c
  r := AlmostRectangle(4, ["...*","....","....","*..."]);
  expect r == ["*..*","....","....","*..*"], "Test 11c failed";

  print "All tests passed\n";
}