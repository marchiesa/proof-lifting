q = int(input())
for _ in range(q):
    a, b = map(int, input().split())
    print((b - a % b) % b)