a, b, c, d = map(int, input().split())
p = (a + 2) * (b + d + 2) - (a - c) * d - a*b - c*d
print(p)