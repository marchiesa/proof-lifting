// --- Specification: models a 24-hour clock and time advancement ---

// A valid 24-hour clock time
ghost predicate ValidTime(h: int, m: int)
{
  0 <= h < 24 && 0 <= m < 60
}

// Total minutes elapsed since midnight for time (h, m)
ghost function MinutesSinceMidnight(h: int, m: int): int
{
  h * 60 + m
}

// Clock state (as minutes since midnight) after advancing n minutes from (h, m)
ghost function ClockStateAfter(h: int, m: int, n: int): int
{
  (MinutesSinceMidnight(h, m) + n) % 1440
}

// Does advancing the clock by exactly n minutes from (h, m) reach midnight (00:00)?
ghost predicate ReachesMidnight(h: int, m: int, n: int)
{
  ClockStateAfter(h, m, n) == 0
}

// --- Implementation ---

method MinutesBeforeNewYear(h: int, m: int) returns (minutes: int)
  requires ValidTime(h, m)
  ensures 1 <= minutes <= 1440
  ensures ReachesMidnight(h, m, minutes)
  ensures forall k | 1 <= k < minutes :: !ReachesMidnight(h, m, k)
{
  minutes := (23 - h) * 60 + (60 - m);
}