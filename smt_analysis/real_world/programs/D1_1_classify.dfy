// Pattern: Classify value into categories based on thresholds
// Source: mcpartools/_analyse_mat_sections (classify material sections)
//         puni/Note._expand_url (classify URL types)
// Real-world: grading, risk assessment, HTTP status classification

method Classify(values: seq<int>) returns (low: int, mid: int, high: int)
  ensures low + mid + high == |values|
  ensures low >= 0 && mid >= 0 && high >= 0
{
  low := 0;
  mid := 0;
  high := 0;
  var i := 0;
  while i < |values|
    invariant 0 <= i <= |values|
    invariant low + mid + high == i
    invariant low >= 0 && mid >= 0 && high >= 0
  {
    if values[i] < 0 {
      low := low + 1;
    } else if values[i] < 100 {
      mid := mid + 1;
    } else {
      high := high + 1;
    }
    i := i + 1;
  }
}
