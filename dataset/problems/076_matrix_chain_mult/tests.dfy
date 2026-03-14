// Matrix Chain Multiplication -- Test cases

method {:axiom} MatrixChain(dims: seq<nat>) returns (cost: nat)
  requires |dims| >= 2

method TestTwo()
{
  // Two matrices: 10x30 and 30x5 => 10*30*5 = 1500
  var c := MatrixChain([10, 30, 5]);
}

method TestThree()
{
  // Classic example: dimensions [10, 30, 5, 60]
  var c := MatrixChain([10, 30, 5, 60]);
}
