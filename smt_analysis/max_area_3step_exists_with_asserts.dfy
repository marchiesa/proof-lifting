function areaFor(height: seq<int>, i: int, j: int): int
  requires 0 <= i && i < j && j < |height|
{
  (if height[i] < height[j] then height[i] else height[j]) * (j - i)
}

// 3 steps, only existential postcondition, WITH 3 asserts
method maxAreaStep(height: seq<int>, i: int, j: int, result: int) returns (result2: int)
  requires 0 <= i < j
  requires j + 2 < |height|
  requires exists x, y :: 0 <= x < y < |height| && result == areaFor(height, x, y)
  ensures exists x, y :: 0 <= x < y < |height| && result2 == areaFor(height, x, y)
{
  var width := j - i;
  var current_height := if height[i] < height[j] then height[i] else height[j];
  var area := width * current_height;
  assert area == areaFor(height, i, j);
  result2 := if result > area then result else area;

  width := (j + 1) - i;
  current_height := if height[i] < height[j + 1] then height[i] else height[j + 1];
  area := width * current_height;
  assert area == areaFor(height, i, j + 1);
  result2 := if result2 > area then result2 else area;

  width := (j + 2) - i;
  current_height := if height[i] < height[j + 2] then height[i] else height[j + 2];
  area := width * current_height;
  assert area == areaFor(height, i, j + 2);
  result2 := if result2 > area then result2 else area;
}
