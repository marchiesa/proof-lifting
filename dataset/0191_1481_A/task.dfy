// --- Formal Specification ---

// Displacement of a single navigation command along each axis
ghost function DeltaX(c: char): int {
  if c == 'R' then 1 else if c == 'L' then -1 else 0
}

ghost function DeltaY(c: char): int {
  if c == 'U' then 1 else if c == 'D' then -1 else 0
}

// Core specification predicate: Can we select a subsequence of commands from s
// whose cumulative displacement equals (px, py)?
// At each position we either skip the command or execute it.
// This directly models the problem: delete some orders from s so that
// the remaining orders move us from (0,0) to (px, py).
ghost predicate CanReachBySubseq(s: string, px: int, py: int)
  decreases |s|
{
  if px == 0 && py == 0 then
    true  // select nothing more; target reached
  else if |s| == 0 then
    false // no commands left but target not reached
  else
    // skip the last command
    CanReachBySubseq(s[..|s|-1], px, py)
    // or execute it (subtract its contribution from remaining target)
    || CanReachBySubseq(s[..|s|-1], px - DeltaX(s[|s|-1]), py - DeltaY(s[|s|-1]))
}

// --- Implementation (bodies unchanged) ---

method CountChar(s: string, c: char) returns (count: int)
{
  count := 0;
  var i := 0;
  while i < |s|
  {
    if s[i] == c {
      count := count + 1;
    }
    i := i + 1;
  }
}

method SpaceNavigation(px: int, py: int, s: string) returns (result: bool)
  ensures result == CanReachBySubseq(s, px, py)
{
  var p := true;
  var rc := CountChar(s, 'R');
  var lc := CountChar(s, 'L');
  var uc := CountChar(s, 'U');
  var dc := CountChar(s, 'D');
  if px > 0 && rc < px { p := false; }
  if px < 0 && lc < -px { p := false; }
  if py > 0 && uc < py { p := false; }
  if py < 0 && dc < -py { p := false; }
  return p;
}