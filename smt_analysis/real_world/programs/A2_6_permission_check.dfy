// Pattern: Check if user has required permissions (all-of check with predicate)
// Source: access control systems, middleware, API gateways
// Real-world: RBAC permission checking, feature flag evaluation

predicate HasPermission(userPerms: seq<int>, required: int)
{
  exists i :: 0 <= i < |userPerms| && userPerms[i] == required
}

predicate HasAllPermissions(userPerms: seq<int>, required: seq<int>)
{
  forall j :: 0 <= j < |required| ==> HasPermission(userPerms, required[j])
}

method CheckPermissions(userPerms: seq<int>, required: seq<int>) returns (allowed: bool)
  ensures allowed <==> HasAllPermissions(userPerms, required)
{
  allowed := true;
  var i := 0;
  while i < |required|
    invariant 0 <= i <= |required|
    invariant allowed <==> HasAllPermissions(userPerms, required[..i])
  {
    var found := false;
    var j := 0;
    while j < |userPerms|
      invariant 0 <= j <= |userPerms|
      invariant !found ==> forall k :: 0 <= k < j ==> userPerms[k] != required[i]
      invariant found ==> HasPermission(userPerms, required[i])
    {
      if userPerms[j] == required[i] {
        assert HasPermission(userPerms, required[i]);  // SMT QUIRK: A2 predicate inst.
        found := true;
        break;
      }
      j := j + 1;
    }
    if !found {
      allowed := false;
      assert !HasPermission(userPerms, required[i]);  // SMT QUIRK: A1 negated existential
      assert !HasAllPermissions(userPerms, required[..i+1]);
      return;
    }
    assert a_help: HasAllPermissions(userPerms, required[..i+1]) by {
      assert required[..i+1] == required[..i] + [required[i]];  // SMT QUIRK: B1 extensionality
      assert HasPermission(userPerms, required[i]);
    }
    i := i + 1;
  }
  assert required[..|required|] == required;  // SMT QUIRK: B1 take-full
}
