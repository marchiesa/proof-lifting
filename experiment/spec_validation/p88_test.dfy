// Helper to compute powers of two
function pow2(m: nat): nat
    decreases m
{
    if m == 0 then 1 else 2 * pow2(m - 1)
}

// Extract the value of the k-th bit (0-based) of x
function bitAt(x: int, k: nat): bool
    requires pow2(k) > 0  // Prevent division by zero
{
    ((x / pow2(k)) % 2) == 1
}

// Two integers differ in exactly one of the first 'bits' bits
predicate oneBitDiff(a: int, b: int, bits: nat)
    requires bits >= 1  // Ensure we have at least one bit to compare
    requires forall k :: 0 <= k < bits ==> pow2(k) > 0  // Ensure pow2(k) > 0 for all relevant k
{
    exists p :: 
        && 0 <= p < bits 
        && bitAt(a, p) != bitAt(b, p)
        && (forall q :: 0 <= q < bits && q != p ==> 
            (var v1 := bitAt(a, q);
             var v2 := bitAt(b, q);
             v1 == v2))
}

// Predicate to establish that pow2 is always positive
predicate pow2IsPositive(n: nat)
{
    forall k :: 0 <= k < n ==> pow2(k) > 0
}

// Complete post-condition for grayCode
predicate grayCodePost(n: nat, result: seq<int>)
    requires n >= 1  // Ensure n is positive
{
    && |result| == pow2(n)  // Length must be 2^n
    && (forall i :: 0 <= i < |result| ==> 0 <= result[i] < pow2(n))  // All values in valid range
    && (forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j])  // All values unique
    && (|result| > 0 ==> result[0] == 0)  // First value must be 0
    && (forall k :: 0 <= k < n ==> pow2(k) > 0)  // Ensure pow2(k) > 0 for all k < n
    && (forall i :: 0 <= i < |result|-1 ==> oneBitDiff(result[i], result[i+1], n))  // Adjacent values differ by one bit
    && (|result| > 0 ==> oneBitDiff(result[|result|-1], result[0], n))  // First and last values differ by one bit
}


// method to be verified
method grayCode(n: nat) returns (result: seq<int>)
requires n >= 1  // As per the constraints: 1 <= n <= 16
ensures grayCodePost(n, result)
{
    var size := 1;
    var i := 0;
    while i < n
    {
        size := size * 2;
        i := i + 1;
    }
    
    result := [];
    i := 0;
    while i < size
    {
        var iAsBV: bv32 := i as bv32;
        var shifted: bv32 := iAsBV >> 1;
        var xored: bv32 := iAsBV ^ shifted;
        result := result + [(xored as int)];
        i := i + 1;
    }
}

method Main()
{
    var result;

    result := grayCode(n:=1);
    if result != [0, 1]
    {
        print("Test failed: with input (\"n\":=1) got: ");
        print(result);
        print(" instead of \"[0, 1]\")\n");
    }

    result := grayCode(n:=2);
    if result != [0, 1, 3, 2]
    {
        print("Test failed: with input (\"n\":=2) got: ");
        print(result);
        print(" instead of \"[0, 1, 3, 2]\")\n");
    }

    result := grayCode(n:=3);
    if result != [0, 1, 3, 2, 6, 7, 5, 4]
    {
        print("Test failed: with input (\"n\":=3) got: ");
        print(result);
        print(" instead of \"[0, 1, 3, 2, 6, 7, 5, 4]\")\n");
    }

    result := grayCode(n:=4);
    if result != [0, 1, 3, 2, 6, 7, 5, 4, 12, 13, 15, 14, 10, 11, 9, 8]
    {
        print("Test failed: with input (\"n\":=4) got: ");
        print(result);
        print(" instead of \"[0, 1, 3, 2, 6, 7, 5, 4, 12, 13, 15, 14, 10, 11, 9, 8]\")\n");
    }

    result := grayCode(n:=5);
    if result != [0, 1, 3, 2, 6, 7, 5, 4, 12, 13, 15, 14, 10, 11, 9, 8, 24, 25, 27, 26, 30, 31, 29, 28, 20, 21, 23, 22, 18, 19, 17, 16]
    {
        print("Test failed: with input (\"n\":=5) got: ");
        print(result);
        print(" instead of \"[0, 1, 3, 2, 6, 7, 5, 4, 12, 13, 15, 14, 10, 11, 9, 8, 24, 25, 27, 26, 30, 31, 29, 28, 20, 21, 23, 22, 18, 19, 17, 16]\")\n");
    }

    result := grayCode(n:=6);
    if result != [0, 1, 3, 2, 6, 7, 5, 4, 12, 13, 15, 14, 10, 11, 9, 8, 24, 25, 27, 26, 30, 31, 29, 28, 20, 21, 23, 22, 18, 19, 17, 16, 48, 49, 51, 50, 54, 55, 53, 52, 60, 61, 63, 62, 58, 59, 57, 56, 40, 41, 43, 42, 46, 47, 45, 44, 36, 37, 39, 38, 34, 35, 33, 32]
    {
        print("Test failed: with input (\"n\":=6) got: ");
        print(result);
        print(" instead of \"[0, 1, 3, 2, 6, 7, 5, 4, 12, 13, 15, 14, 10, 11, 9, 8, 24, 25, 27, 26, 30, 31, 29, 28, 20, 21, 23, 22, 18, 19, 17, 16, 48, 49, 51, 50, 54, 55, 53, 52, 60, 61, 63, 62, 58, 59, 57, 56, 40, 41, 43, 42, 46, 47, 45, 44, 36, 37, 39, 38, 34, 35, 33, 32]\")\n");
    }

}
