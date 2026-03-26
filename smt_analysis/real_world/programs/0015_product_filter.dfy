// Source: cgtobi/PyRMVtransport/_product_filter
// URL: https://github.com/cgtobi/PyRMVtransport/blob/20a0d68ecfdedceb32e8ca96c381fdec7e2069c7/RMVtransport/rmvtransport.py#L172-L177
// Original: sum of product values from a set, used as a bitmask filter
// Gist: _filter = 0; for product in products: _filter += product

ghost function Sum(s: seq<int>): int
{
  if |s| == 0 then 0 else Sum(s[..|s|-1]) + s[|s|-1]
}

method ProductFilter(products: seq<int>) returns (filter: int)
  ensures filter == Sum(products)
{
  filter := 0;
  var i := 0;
  while i < |products|
    invariant 0 <= i <= |products|
    invariant filter == Sum(products[..i])
  {
    assert products[..i+1] == products[..i] + [products[i]];
    filter := filter + products[i];
    i := i + 1;
  }
  assert products[..|products|] == products;
}
