// Pattern: Compute area/product of two positive values
// Source: pyefd/normalize_efd (Fourier coefficient normalization)
//         various geometry/graphics libraries
// Real-world: layout computation, resource allocation, pricing

method ComputeArea(width: int, height: int) returns (area: int)
  requires width > 0 && height > 0
  ensures area > 0
  ensures area == width * height
{
  area := width * height;
  assert width >= 1 && height >= 1;  // SMT QUIRK: C1 NLA — Z3 can't prove a*b > 0 from a>0, b>0
}
