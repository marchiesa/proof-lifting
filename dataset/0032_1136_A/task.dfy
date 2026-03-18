// A chapter is not completely read if it contains at least one unread page.
// Page p is unread when p >= k (k is the first unread page).
ghost predicate ChapterNotCompletelyRead(chapter: (int, int), k: int)
{
  exists p | chapter.0 <= p <= chapter.1 :: p >= k
}

// Count chapters that are not completely read.
ghost function CountNotCompletelyRead(chapters: seq<(int, int)>, k: int): int
  decreases |chapters|
{
  if |chapters| == 0 then 0
  else
    CountNotCompletelyRead(chapters[..|chapters|-1], k)
    + (if ChapterNotCompletelyRead(chapters[|chapters|-1], k) then 1 else 0)
}

method NastyaBook(chapters: seq<(int, int)>, k: int) returns (count: int)
  requires forall i | 0 <= i < |chapters| :: chapters[i].0 <= chapters[i].1
  requires forall i | 0 <= i < |chapters| - 1 :: chapters[i].1 < chapters[i+1].0
  requires k >= 1
  ensures count == CountNotCompletelyRead(chapters, k)
{
  var i := 0;
  while i < |chapters|
  {
    var (_, y) := chapters[i];
    if y >= k {
      count := |chapters| - i;
      return;
    }
    i := i + 1;
  }
  count := 0;
  return;
}