// Source: asweigart/pysimplevalidate/_prevalidationCheck
// URL: https://github.com/asweigart/pysimplevalidate/blob/3ca27228abb7355d14bbf8abc225c63366379e44/src/pysimplevalidate/__init__.py#L113-L164
// Original: Validate value against allowlist then blocklist
// Gist: check allowlist first (return True if match), then blocklist (reject if match)

// Model: value is an int, allowlist/blocklist are seq<int>
predicate InList(value: int, list: seq<int>) {
  exists i :: 0 <= i < |list| && list[i] == value
}

predicate Allowed(value: int, allowlist: seq<int>, blocklist: seq<int>) {
  InList(value, allowlist) || !InList(value, blocklist)
}

method PrevalidationCheck(value: int, allowlist: seq<int>, blocklist: seq<int>)
    returns (accepted: bool)
  ensures accepted <==> Allowed(value, allowlist, blocklist)
{
  // Check allowlist first
  var i := 0;
  while i < |allowlist|
    invariant 0 <= i <= |allowlist|
    invariant forall j :: 0 <= j < i ==> allowlist[j] != value
  {
    if allowlist[i] == value {
      assert InList(value, allowlist);
      accepted := true;
      return;
    }
    i := i + 1;
  }
  assert !InList(value, allowlist);

  // Check blocklist
  i := 0;
  while i < |blocklist|
    invariant 0 <= i <= |blocklist|
    invariant forall j :: 0 <= j < i ==> blocklist[j] != value
  {
    if blocklist[i] == value {
      assert InList(value, blocklist);
      accepted := false;
      return;
    }
    i := i + 1;
  }
  assert !InList(value, blocklist);
  accepted := true;
}
