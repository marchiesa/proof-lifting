ghost predicate OnBorder(r: int, c: int, top: int, left: int, rows: int, cols: int)
{
  rows >= 1 && cols >= 1 &&
  top <= r < top + rows && left <= c < left + cols &&
  (r == top || r == top + rows - 1 || c == left || c == left + cols - 1)
}

ghost predicate InRing(r: int, c: int, w: int, h: int, ring: int)
{
  OnBorder(r, c, 2 * ring, 2 * ring, h - 4 * ring, w - 4 * ring)
}

ghost predicate IsGilded(r: int, c: int, w: int, h: int, k: int)
{
  exists i | 0 <= i < k :: InRing(r, c, w, h, i)
}

ghost function CountGildedUpTo(w: int, h: int, k: int, n: int): int
  requires w >= 1 && h >= 1 && 0 <= n <= w * h
  decreases n
{
  if n == 0 then 0
  else
    var r := (n - 1) / w;
    var c := (n - 1) % w;
    CountGildedUpTo(w, h, k, n - 1) + (if IsGilded(r, c, w, h, k) then 1 else 0)
}

ghost function CountGilded(w: int, h: int, k: int): int
  requires w >= 1 && h >= 1
{
  CountGildedUpTo(w, h, k, w * h)
}

method {:verify false} GoldenPlate(w: int, h: int, k: int) returns (gilded: int)
  requires w >= 1 && h >= 1 && k >= 0
  ensures gilded == CountGilded(w, h, k)
{
  gilded := 0;
  var ww := w;
  var hh := h;
  var i := 0;
  while i < k
  {
    var minWH := if ww < hh then ww else hh;
    var maxWH := if ww > hh then ww else hh;
    if minWH == 1 {
      gilded := gilded + maxWH;
    } else {
      gilded := gilded + 2 * (ww + hh) - 4;
    }
    ww := ww - 4;
    hh := hh - 4;
    i := i + 1;
  }
}