method YetAnotherStringGame(s: string) returns (result: string)
{
  result := "";
  for i := 0 to |s| {
    if i % 2 == 0 {
      if s[i] != 'a' {
        result := result + ['a'];
      } else {
        result := result + ['b'];
      }
    } else {
      if s[i] != 'z' {
        result := result + ['z'];
      } else {
        result := result + ['y'];
      }
    }
  }
}

method Main()
{
  // Test 1
  var r := YetAnotherStringGame("a");
  expect r == "b", "Test 1.1 failed";

  r := YetAnotherStringGame("bbbb");
  expect r == "azaz", "Test 1.2 failed";

  r := YetAnotherStringGame("az");
  expect r == "by", "Test 1.3 failed";

  // Test 2
  r := YetAnotherStringGame("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
  expect r == "bzbzbzbzbzbzbzbzbzbzbzbzbzbzbzbzbzbzbzbzbzbzbzbzbz", "Test 2.1 failed";

  r := YetAnotherStringGame("zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz");
  expect r == "ayayayayayayayayayayayayayayayayayayayayayayayayay", "Test 2.2 failed";

  r := YetAnotherStringGame("azazazazazazazazazazazazazazazazazazazazazazazazaz");
  expect r == "bybybybybybybybybybybybybybybybybybybybybybybybyby", "Test 2.3 failed";

  r := YetAnotherStringGame("zazazazazazazazazazazazazazazazazazazazazazazazaza");
  expect r == "azazazazazazazazazazazazazazazazazazazazazazazazaz", "Test 2.4 failed";

  r := YetAnotherStringGame("zzazzazzazzazzazzazzazzazzazzazzazzazzazzazza");
  expect r == "aybyazaybyazaybyazaybyazaybyazaybyazaybyazayb", "Test 2.5 failed";

  // Test 3
  r := YetAnotherStringGame("a");
  expect r == "b", "Test 3 failed";

  // Test 4
  r := YetAnotherStringGame("z");
  expect r == "a", "Test 4 failed";

  // Test 5
  r := YetAnotherStringGame("abcde");
  expect r == "bzaza", "Test 5 failed";

  // Test 6
  r := YetAnotherStringGame("zzzzz");
  expect r == "ayaya", "Test 6 failed";

  // Test 7
  r := YetAnotherStringGame("ab");
  expect r == "bz", "Test 7 failed";

  // Test 8
  r := YetAnotherStringGame("ba");
  expect r == "az", "Test 8 failed";

  // Test 9
  r := YetAnotherStringGame("mmmm");
  expect r == "azaz", "Test 9 failed";

  // Test 10
  r := YetAnotherStringGame("abc");
  expect r == "bza", "Test 10.1 failed";

  r := YetAnotherStringGame("xyz");
  expect r == "aza", "Test 10.2 failed";

  // Test 11
  r := YetAnotherStringGame("a");
  expect r == "b", "Test 11.1 failed";

  r := YetAnotherStringGame("bb");
  expect r == "az", "Test 11.2 failed";

  r := YetAnotherStringGame("ccc");
  expect r == "aza", "Test 11.3 failed";

  // Test 12
  r := YetAnotherStringGame("hello");
  expect r == "azaza", "Test 12.1 failed";

  r := YetAnotherStringGame("world");
  expect r == "azaza", "Test 12.2 failed";

  r := YetAnotherStringGame("az");
  expect r == "by", "Test 12.3 failed";

  r := YetAnotherStringGame("za");
  expect r == "az", "Test 12.4 failed";

  r := YetAnotherStringGame("abcdefghij");
  expect r == "bzazazazaz", "Test 12.5 failed";

  print "All tests passed\n";
}