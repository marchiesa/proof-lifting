t = int(input())

for case in range(t):
    n, k = map(int, input().split())
    a = [int(x) for x in input().split()]

    m = min(a)
    out = 0
    for x in a:
        out += (k - x) // m

    out -= (k - m) // m
    print(out)