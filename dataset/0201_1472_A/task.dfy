// The maximum number of pieces obtainable from a single sheet of size w × h
// by repeatedly applying the problem's cutting rules:
//   - If w is even, cut to get two sheets of (w/2) × h
//   - If h is even, cut to get two sheets of w × (h/2)
// Cutting produces two identical sub-sheets, each independently cuttable,
// so total pieces from one cut = 2 × MaxPieces(sub-sheet).
// When both cuts are available, we take the option yielding more pieces.
ghost function MaxPieces(w: int, h: int): int
  requires w > 0 && h > 0
  decreases w + h
{
  if w % 2 == 0 && h % 2 == 0 then
    var viaW := 2 * MaxPieces(w / 2, h);
    var viaH := 2 * MaxPieces(w, h / 2);
    if viaW >= viaH then viaW else viaH
  else if w % 2 == 0 then
    2 * MaxPieces(w / 2, h)
  else if h % 2 == 0 then
    2 * MaxPieces(w, h / 2)
  else
    1
}

method CardsForFriends(w: int, h: int, n: int) returns (result: bool)
  requires w > 0 && h > 0
  ensures result == (MaxPieces(w, h) >= n)
{
  var cnt := 1;
  var ww := w;
  var hh := h;
  while ww > 0 && ww % 2 == 0
  {
    cnt := cnt * 2;
    ww := ww / 2;
  }
  while hh > 0 && hh % 2 == 0
  {
    cnt := cnt * 2;
    hh := hh / 2;
  }
  result := cnt >= n;
}