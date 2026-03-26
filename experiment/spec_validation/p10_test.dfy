function area(height: seq<int>, i: int, j: int): int
    requires 0 <= i < j < |height|
{
    (j - i) * (if height[i] < height[j] then height[i] else height[j])
}

predicate maxAreaPost(height: seq<int>, maxWaterArea: int)
{
    |height| >= 2                                      
    &&
    (exists i, j: int :: 
        0 <= i < j < |height| 
        && maxWaterArea == area(height, i, j))
    &&
    (forall i, j: int :: 
        0 <= i < j < |height| ==> area(height, i, j) <= maxWaterArea)
}

// method to be verified
method maxArea(height: seq<int>) returns (maxWaterArea: int)
    requires |height| >= 2
    ensures maxAreaPost(height, maxWaterArea)
{
    var left := 0;
    var right := |height| - 1;
    maxWaterArea := 0;
    
    while left < right
    {
        var width := right - left;
        var h := if height[left] < height[right] then height[left] else height[right];
        var area := width * h;
        
        maxWaterArea := if area > maxWaterArea then area else maxWaterArea;
        
        if height[left] < height[right] {
            left := left + 1;
        } else {
            right := right - 1;
        }
    }
}

method Main()
{
    var result;

    result := maxArea(height:=[1, 1]);
    if result != 1
    {
        print("Test failed: with input (\"height\":=[1, 1]) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := maxArea(height:=[1, 8, 6, 2, 5, 4, 8, 3, 7]);
    if result != 49
    {
        print("Test failed: with input (\"height\":=[1, 8, 6, 2, 5, 4, 8, 3, 7]) got: ");
        print(result);
        print(" instead of \"49\")\n");
    }

    result := maxArea(height:=[0, 0, 0, 0, 0]);
    if result != 0
    {
        print("Test failed: with input (\"height\":=[0, 0, 0, 0, 0]) got: ");
        print(result);
        print(" instead of \"0\")\n");
    }

    result := maxArea(height:=[10000, 10000]);
    if result != 10000
    {
        print("Test failed: with input (\"height\":=[10000, 10000]) got: ");
        print(result);
        print(" instead of \"10000\")\n");
    }

    result := maxArea(height:=[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    if result != 25
    {
        print("Test failed: with input (\"height\":=[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) got: ");
        print(result);
        print(" instead of \"25\")\n");
    }

    result := maxArea(height:=[10, 9, 8, 7, 6, 5, 4, 3, 2, 1]);
    if result != 25
    {
        print("Test failed: with input (\"height\":=[10, 9, 8, 7, 6, 5, 4, 3, 2, 1]) got: ");
        print(result);
        print(" instead of \"25\")\n");
    }

    result := maxArea(height:=[0, 10000, 0, 10000]);
    if result != 20000
    {
        print("Test failed: with input (\"height\":=[0, 10000, 0, 10000]) got: ");
        print(result);
        print(" instead of \"20000\")\n");
    }

    result := maxArea(height:=[1, 8, 6, 2, 5, 4, 8, 3, 7, 1]);
    if result != 49
    {
        print("Test failed: with input (\"height\":=[1, 8, 6, 2, 5, 4, 8, 3, 7, 1]) got: ");
        print(result);
        print(" instead of \"49\")\n");
    }

}
