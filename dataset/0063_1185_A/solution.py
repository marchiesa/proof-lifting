a, b, c, d = map(int, input().split())

if a > b:
    a, b = b, a
if b > c:
    b, c = c, b
if a > b:
    a, b = b, a

print(max(0, d - abs(a - b)) + max(0, d - abs(b - c)))