// A valid assignment: enough pens for all lectures, enough pencils for all
// practical classes, and they fit in the pencilcase.
ghost predicate ValidAssignment(x: int, y: int, a: int, b: int, c: int, d: int, k: int)
{
  x >= 0 && y >= 0 && x * c >= a && y * d >= b && x + y <= k
}

// The problem is feasible iff some valid assignment of pens and pencils exists.
ghost predicate Feasible(a: int, b: int, c: int, d: int, k: int)
{
  exists x :: exists y :: ValidAssignment(x, y, a, b, c, d, k)
}

method PensAndPencils(a: int, b: int, c: int, d: int, k: int) returns (x: int, y: int)
  requires a >= 1 && b >= 1 && c >= 1 && d >= 1 && k >= 1
  ensures Feasible(a, b, c, d, k) ==> ValidAssignment(x, y, a, b, c, d, k)
  ensures !Feasible(a, b, c, d, k) ==> x == -1
{
  var pens := (a + c - 1) / c;
  var pencils := (b + d - 1) / d;
  if pens + pencils <= k {
    return pens, pencils;
  } else {
    return -1, 0;
  }
}