method Hotelier(events: seq<char>) returns (rooms: seq<int>)
  ensures |rooms| == 10
  ensures rooms == HotelAfterEvents(events)
{
  rooms := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
  var idx := 0;
  while idx < |events|
    invariant 0 <= idx <= |events|
    invariant |rooms| == 10
    invariant rooms == HotelAfterEvents(events[..idx])
  {
    ghost var old_rooms := rooms;
    var ch := events[idx];
    if ch == 'L' {
      var i := 0;
      var found := false;
      while i < 10 && !found
        invariant 0 <= i <= 10
        invariant |rooms| == 10
        invariant !found ==> rooms == old_rooms
        invariant !found ==> forall j :: 0 <= j < i ==> old_rooms[j] != 0
        invariant found ==> rooms == HotelAfterEvent(old_rooms, 'L')
        decreases !found, 10 - i
      {
        if rooms[i] == 0 {
          LeftmostEmptyIs(old_rooms, i);
          rooms := rooms[i := 1];
          found := true;
        } else {
          i := i + 1;
        }
      }
      if !found {
        LeftmostEmptyNone(old_rooms);
      }
    } else if ch == 'R' {
      var i := 9;
      var found := false;
      while i >= 0 && !found
        invariant -1 <= i <= 9
        invariant |rooms| == 10
        invariant !found ==> rooms == old_rooms
        invariant !found ==> forall j :: i < j < 10 ==> old_rooms[j] != 0
        invariant found ==> rooms == HotelAfterEvent(old_rooms, 'R')
        decreases !found, i + 1
      {
        if rooms[i] == 0 {
          RightmostEmptyIs(old_rooms, i);
          rooms := rooms[i := 1];
          found := true;
        } else {
          i := i - 1;
        }
      }
      if !found {
        RightmostEmptyNone(old_rooms);
      }
    } else if '0' <= ch <= '9' {
      var i := (ch as int) - ('0' as int);
      rooms := rooms[i := 0];
    }
    assert rooms == HotelAfterEvent(old_rooms, ch);

    idx := idx + 1;
  }

}
</DA