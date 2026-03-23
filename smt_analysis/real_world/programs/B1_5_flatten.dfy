// Pattern: Flatten nested sequences
// Source: geojsoncontour/contourf_to_geojson_overlap (flatten polygon paths)
//         various data processing pipelines
// Real-world: nested JSON processing, tree traversal results, batch processing

ghost function SumLengths(seqs: seq<seq<int>>): int
{
  if |seqs| == 0 then 0
  else SumLengths(seqs[..|seqs|-1]) + |seqs[|seqs|-1]|
}

method Flatten(seqs: seq<seq<int>>) returns (result: seq<int>)
  ensures |result| == SumLengths(seqs)
{
  result := [];
  var i := 0;
  while i < |seqs|
    invariant 0 <= i <= |seqs|
    invariant |result| == SumLengths(seqs[..i])
  {
    assert seqs[..i+1] == seqs[..i] + [seqs[i]];  // SMT QUIRK: B1 sequence extensionality
    result := result + seqs[i];
    i := i + 1;
  }
  assert seqs[..|seqs|] == seqs;  // SMT QUIRK: B1 take-full
}
