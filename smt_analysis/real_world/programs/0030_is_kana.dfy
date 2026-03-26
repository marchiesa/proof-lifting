// Source: letuananh/chirptext/is_kana
// URL: https://github.com/letuananh/chirptext/blob/ce60b47257b272a587c8703ea1f86cd1a45553a7/chirptext/deko.py#L62-L71
// Original: Check if text is written in kana only (hiragana & katakana)
// Gist: for c in text: if c not in HIRAGANA and c not in KATAKANA: return False

// Model: hiragana = [0..80), katakana = [80..160), other = [160+)
predicate IsKana(c: int) {
  0 <= c < 160
}

predicate AllKana(text: seq<int>) {
  forall i :: 0 <= i < |text| ==> IsKana(text[i])
}

method CheckAllKana(text: seq<int>) returns (result: bool)
  ensures result <==> AllKana(text)
{
  result := true;
  var i := 0;
  while i < |text|
    invariant 0 <= i <= |text|
    invariant result <==> AllKana(text[..i])
  {
    if !IsKana(text[i]) {
      assert !IsKana(text[i]);
      assert text[..i+1] == text[..i] + [text[i]];
      assert !AllKana(text[..i+1]);
      result := false;
      return;
    }
    assert text[..i+1] == text[..i] + [text[i]];
    i := i + 1;
  }
  assert text[..|text|] == text;
}
