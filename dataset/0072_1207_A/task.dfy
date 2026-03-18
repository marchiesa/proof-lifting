ghost predicate ValidAllocation(b: int, p: int, f: int, ham: int, chicken: int)
{
  ham >= 0 && chicken >= 0 &&
  ham <= p && chicken <= f &&
  2 * ham + 2 * chicken <= b
}

ghost function AllocationProfit(ham: int, chicken: int, h: int, c: int): int
{
  ham * h + chicken * c
}

ghost predicate IsMaxProfit(b: int, p: int, f: int, h: int, c: int, profit: int)
{
  (exists ham: int ::
    exists chicken: int ::
      ValidAllocation(b, p, f, ham, chicken) &&
      AllocationProfit(ham, chicken, h, c) == profit)
  &&
  (forall ham: int ::
    forall chicken: int ::
      !ValidAllocation(b, p, f, ham, chicken) ||
      AllocationProfit(ham, chicken, h, c) <= profit)
}

method MaxProfit(b: int, p: int, f: int, h: int, c: int) returns (profit: int)
  requires b >= 0 && p >= 0 && f >= 0 && h >= 0 && c >= 0
  ensures IsMaxProfit(b, p, f, h, c, profit)
{
  var lb := b;
  var lp := p;
  var lf := f;
  var lh := h;
  var lc := c;

  if lh < lc {
    var tmp := lh;
    lh := lc;
    lc := tmp;
    tmp := lp;
    lp := lf;
    lf := tmp;
  }

  var ham := lp;
  if lb / 2 < ham {
    ham := lb / 2;
  }
  profit := ham * lh;
  lb := lb - 2 * ham;

  var chicken := lf;
  if lb / 2 < chicken {
    chicken := lb / 2;
  }
  profit := profit + chicken * lc;
}