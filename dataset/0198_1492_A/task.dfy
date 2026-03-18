ghost predicate SwimmerAtLeft(time: int, period: int)
  requires period > 0
  requires time >= 0
{
  time % period == 0
}

ghost predicate SomeSwimmerAtLeft(time: int, a: int, b: int, c: int)
  requires a > 0 && b > 0 && c > 0
  requires time >= 0
{
  SwimmerAtLeft(time, a) || SwimmerAtLeft(time, b) || SwimmerAtLeft(time, c)
}

ghost predicate IsMinimumWait(p: int, a: int, b: int, c: int, wait: int)
  requires p >= 1 && a > 0 && b > 0 && c > 0
{
  wait >= 0 &&
  SomeSwimmerAtLeft(p + wait, a, b, c) &&
  forall w :: 0 <= w < wait ==> !SomeSwimmerAtLeft(p + w, a, b, c)
}

method ThreeSwimmers(p: int, a: int, b: int, c: int) returns (wait: int)
  requires p >= 1 && a > 0 && b > 0 && c > 0
  ensures IsMinimumWait(p, a, b, c, wait)
{
  var wa := (a - p % a) % a;
  var wb := (b - p % b) % b;
  var wc := (c - p % c) % c;
  wait := wa;
  if wb < wait { wait := wb; }
  if wc < wait { wait := wc; }
}