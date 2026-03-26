function areaFor(height: seq<int>, i: int, j: int): int
  requires 0 <= i && i < j && j < |height|
{
  (if height[i] < height[j] then height[i] else height[j]) * (j - i)
}

// 3 steps: j, j+5, j+10
method maxAreaStep(height: seq<int>, i: int, j: int, result: int) returns (result2: int)
  requires 0 <= i < j
  requires j + 10 < |height|
  requires exists x, y :: 0 <= x < y < |height| && result == areaFor(height, x, y)
  ensures result2 >= areaFor(height, i, j)
  ensures result2 >= areaFor(height, i, j + 5)
  ensures result2 >= areaFor(height, i, j + 10)
  ensures exists x, y :: 0 <= x < y < |height| && result2 == areaFor(height, x, y)
{
  var width := j - i;
  var current_height := if height[i] < height[j] then height[i] else height[j];
  var area := width * current_height;
  result2 := if result > area then result else area;

  width := (j + 5) - i;
  current_height := if height[i] < height[j + 5] then height[i] else height[j + 5];
  area := width * current_height;
  result2 := if result2 > area then result2 else area;

  width := (j + 10) - i;
  current_height := if height[i] < height[j + 10] then height[i] else height[j + 10];
  area := width * current_height;
  result2 := if result2 > area then result2 else area;
}
