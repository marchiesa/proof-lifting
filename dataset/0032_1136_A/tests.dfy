predicate ChapterNotCompletelyRead(chapter: (int, int), k: int)
{
  exists p | chapter.0 <= p <= chapter.1 :: p >= k
}

function CountNotCompletelyRead(chapters: seq<(int, int)>, k: int): int
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

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // Small inputs: CountNotCompletelyRead(chapters, k) == expected

  // From Test 1: 3 chapters all not completely read (k low)
  expect CountNotCompletelyRead([(1,2),(3,4),(5,5)], 1) == 3, "spec positive 1";

  // From Test 2: 3 chapters, 2 not completely read
  expect CountNotCompletelyRead([(1,2),(3,4),(5,5)], 4) == 2, "spec positive 2";

  // From Test 3: 1 chapter not completely read
  expect CountNotCompletelyRead([(1,5)], 4) == 1, "spec positive 3";

  // From Test 4: 3 chapters all not completely read (k in first chapter range)
  expect CountNotCompletelyRead([(1,2),(3,3),(4,5)], 2) == 3, "spec positive 4";

  // From Test 5: 3 chapters, only last not completely read
  expect CountNotCompletelyRead([(1,2),(3,4),(5,5)], 5) == 1, "spec positive 5";

  // From Test 6: 3 chapters, 2 not completely read (k in middle)
  expect CountNotCompletelyRead([(1,1),(2,3),(4,5)], 3) == 2, "spec positive 6";

  // From Test 7: all chapters not completely read (k at start)
  expect CountNotCompletelyRead([(1,2),(3,4),(5,5)], 2) == 3, "spec positive 7";

  // From Test 8: only last chapter not completely read
  expect CountNotCompletelyRead([(1,1),(2,3),(4,5)], 5) == 1, "spec positive 8";

  // Edge: empty sequence
  expect CountNotCompletelyRead([], 1) == 0, "spec positive 9";

  // Edge: all chapters completely read (k beyond all pages)
  expect CountNotCompletelyRead([(1,2),(3,4)], 5) == 0, "spec positive 10";

  // === SPEC NEGATIVE TESTS ===
  // Small inputs: CountNotCompletelyRead(chapters, k) != wrong_output

  // From Negative 1: correct=3, wrong=4
  expect CountNotCompletelyRead([(1,2),(3,4),(5,5)], 1) != 4, "spec negative 1";

  // From Negative 2: correct=2, wrong=3
  expect CountNotCompletelyRead([(1,2),(3,4),(5,5)], 4) != 3, "spec negative 2";

  // From Negative 3: correct=1, wrong=2
  expect CountNotCompletelyRead([(1,5)], 4) != 2, "spec negative 3";

  // From Negative 4: correct=3, wrong=4
  expect CountNotCompletelyRead([(1,2),(3,3),(4,5)], 2) != 4, "spec negative 4";

  // From Negative 5: correct=1, wrong=2
  expect CountNotCompletelyRead([(1,2),(3,4),(5,5)], 5) != 2, "spec negative 5";

  // From Negative 6: correct=2, wrong=3
  expect CountNotCompletelyRead([(1,1),(2,3),(4,5)], 3) != 3, "spec negative 6";

  // From Negative 7: correct=3, wrong=4 (all chapters, wrong by +1)
  expect CountNotCompletelyRead([(1,2),(3,4),(5,5)], 2) != 4, "spec negative 7";

  // From Negative 8: correct=1, wrong=2
  expect CountNotCompletelyRead([(1,1),(2,3),(4,5)], 5) != 2, "spec negative 8";

  // From Negative 9: correct=0, wrong=1 (all read, claiming 1)
  expect CountNotCompletelyRead([(1,2),(3,4)], 5) != 1, "spec negative 9";

  // From Negative 10: correct=0, wrong=1
  expect CountNotCompletelyRead([(1,3)], 4) != 1, "spec negative 10";

  // === IMPLEMENTATION TESTS ===

  var r1 := NastyaBook([(1,3),(4,7),(8,11)], 2);
  expect r1 == 3, "impl test 1 failed";

  var r2 := NastyaBook([(1,4),(5,9),(10,12)], 9);
  expect r2 == 2, "impl test 2 failed";

  var r3 := NastyaBook([(1,7)], 4);
  expect r3 == 1, "impl test 3 failed";

  var r4 := NastyaBook([(1,6),(7,16),(17,20)], 4);
  expect r4 == 3, "impl test 4 failed";

  var r5 := NastyaBook([(1,6),(7,13),(14,17)], 16);
  expect r5 == 1, "impl test 5 failed";

  var r6 := NastyaBook([(1,6),(7,12),(13,19),(20,28),(29,37),(38,39)], 21);
  expect r6 == 3, "impl test 6 failed";

  var r7 := NastyaBook([(1,46),(47,111),(112,207),(208,266),(267,341),(342,380),(381,443),(444,476),(477,495),(496,581),(582,653),(654,710),(711,712),(713,774),(775,799),(800,809),(810,874),(875,877),(878,913),(914,986),(987,998),(999,1030),(1031,1095),(1096,1106),(1107,1147),(1148,1196),(1197,1210)], 45);
  expect r7 == 27, "impl test 7 failed";

  var r8 := NastyaBook([(1,60),(61,84),(85,88),(89,149),(150,216),(217,243),(244,307),(308,319),(320,321),(322,402)], 389);
  expect r8 == 1, "impl test 8 failed";

  var r9 := NastyaBook([(1,17),(18,115),(116,211),(212,269),(270,345),(346,404),(405,441),(442,467),(468,526),(527,583),(584,664),(665,757),(758,794),(795,802),(803,882),(883,920),(921,960),(961,962),(963,1006),(1007,1081),(1082,1112),(1113,1149),(1150,1217),(1218,1282),(1283,1287),(1288,1365),(1366,1374),(1375,1379),(1380,1478),(1479,1524),(1525,1549),(1550,1646),(1647,1671),(1672,1752),(1753,1755),(1756,1782),(1783,1824),(1825,1894),(1895,1966),(1967,2027),(2028,2091),(2092,2112),(2113,2153),(2154,2156),(2157,2161),(2162,2258),(2259,2324),(2325,2421),(2422,2501)], 1285);
  expect r9 == 25, "impl test 9 failed";

  var r10 := NastyaBook([(1,48),(49,118),(119,122),(123,198),(199,283),(284,352),(353,447),(448,528),(529,539),(540,549),(550,557),(558,627),(628,700),(701,741),(742,835),(836,883),(884,887),(888,900),(901,943),(944,1032),(1033,1131),(1132,1158),(1159,1222),(1223,1281),(1282,1315),(1316,1397),(1398,1469),(1470,1520),(1521,1558),(1559,1631),(1632,1688),(1689,1699),(1700,1766),(1767,1775),(1776,1778),(1779,1878),(1879,1904),(1905,1984),(1985,1987),(1988,1999),(2000,2059),(2060,2126),(2127,2168),(2169,2189),(2190,2206)], 1109);
  expect r10 == 25, "impl test 10 failed";

  var r11 := NastyaBook([(1,1),(2,2),(3,3),(4,4),(5,5),(6,6),(7,7),(8,8),(9,9),(10,10),(11,11),(12,12),(13,13),(14,14),(15,15),(16,16),(17,17),(18,18),(19,19)], 13);
  expect r11 == 7, "impl test 11 failed";

  var r12 := NastyaBook([(1,1),(2,2),(3,3),(4,4),(5,5),(6,6),(7,7),(8,8),(9,9),(10,10),(11,11),(12,12),(13,13),(14,14),(15,15),(16,16),(17,17),(18,18),(19,19),(20,20),(21,21),(22,22),(23,23),(24,24),(25,25),(26,26),(27,27)], 25);
  expect r12 == 3, "impl test 12 failed";

  var r13 := NastyaBook([(1,1),(2,2),(3,3),(4,4),(5,5),(6,6),(7,7),(8,8),(9,9),(10,10),(11,11),(12,12),(13,13),(14,14),(15,15),(16,16),(17,17),(18,18),(19,19),(20,20),(21,21),(22,22),(23,23),(24,24),(25,25),(26,26),(27,27),(28,28),(29,29),(30,30),(31,31),(32,32),(33,33),(34,34),(35,35),(36,36),(37,37),(38,38),(39,39),(40,40),(41,41),(42,42),(43,43),(44,44),(45,45),(46,46),(47,47),(48,48),(49,49),(50,50),(51,51),(52,52),(53,53),(54,54),(55,55),(56,56),(57,57),(58,58),(59,59),(60,60),(61,61),(62,62),(63,63),(64,64),(65,65),(66,66),(67,67),(68,68),(69,69),(70,70),(71,71)], 69);
  expect r13 == 3, "impl test 13 failed";

  var r14 := NastyaBook([(1,1),(2,2),(3,3),(4,4),(5,5),(6,6),(7,7),(8,8),(9,9),(10,10),(11,11),(12,12)], 9);
  expect r14 == 4, "impl test 14 failed";

  var r15 := NastyaBook([(1,1),(2,2),(3,3),(4,4),(5,5),(6,6),(7,7),(8,8),(9,9),(10,10),(11,11),(12,12),(13,13),(14,14),(15,15),(16,16),(17,17),(18,18),(19,19),(20,20),(21,21),(22,22),(23,23),(24,24),(25,25),(26,26),(27,27),(28,28),(29,29),(30,30),(31,31),(32,32),(33,33),(34,34),(35,35),(36,36),(37,37),(38,38),(39,39),(40,40),(41,41),(42,42),(43,43),(44,44),(45,45),(46,46),(47,47),(48,48),(49,49),(50,50),(51,51),(52,52),(53,53),(54,54),(55,55),(56,56),(57,57),(58,58),(59,59),(60,60),(61,61),(62,62),(63,63),(64,64),(65,65),(66,66),(67,67),(68,68)], 53);
  expect r15 == 16, "impl test 15 failed";

  var r16 := NastyaBook([(1,12),(13,59),(60,100),(101,124)], 93);
  expect r16 == 2, "impl test 16 failed";

  var r17 := NastyaBook([(1,81),(82,177),(178,254),(255,338),(339,410),(411,412),(413,474),(475,534),(535,555)], 426);
  expect r17 == 3, "impl test 17 failed";

  var r18 := NastyaBook([(1,48),(49,138),(139,146),(147,200),(201,272)], 122);
  expect r18 == 4, "impl test 18 failed";

  var r19 := NastyaBook([(1,6),(7,14),(15,21),(22,24),(25,27),(28,31),(32,39),(40,40),(41,43),(44,48),(49,52),(53,54),(55,60),(61,68),(69,74),(75,80),(81,82),(83,89),(90,90),(91,97),(98,101),(102,111),(112,120),(121,130),(131,135),(136,141),(142,150),(151,153),(154,156),(157,157),(158,162),(163,164),(165,165),(166,167),(168,170),(171,171),(172,181),(182,188),(189,195),(196,202),(203,203),(204,208),(209,218),(219,220),(221,230),(231,237),(238,239)], 161);
  expect r19 == 17, "impl test 19 failed";

  var r20 := NastyaBook([(1,8),(9,15),(16,18),(19,23),(24,25),(26,27),(28,29),(30,36),(37,39),(40,44),(45,54)], 49);
  expect r20 == 1, "impl test 20 failed";

  print "All tests passed\n";
}