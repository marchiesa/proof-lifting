// Source: alefnula/tea/get_exception
// URL: https://github.com/alefnula/tea/blob/f5a0a724a425ec4f9dd2c7fe966ef06faf3a15a3/tea/utils/__init__.py#L177-L189
// Original: Concatenate list of strings: for entry in list: result += entry
// Gist: Build one string from a list of parts (traceback formatting)

ghost function Concat(parts: seq<seq<int>>): seq<int>
{
  if |parts| == 0 then []
  else Concat(parts[..|parts|-1]) + parts[|parts|-1]
}

method ConcatAll(parts: seq<seq<int>>) returns (result: seq<int>)
  ensures result == Concat(parts)
{
  result := [];
  var i := 0;
  while i < |parts|
    invariant 0 <= i <= |parts|
    invariant result == Concat(parts[..i])
  {
    assert parts[..i+1] == parts[..i] + [parts[i]];
    result := result + parts[i];
    i := i + 1;
  }
  assert parts[..|parts|] == parts;
}
