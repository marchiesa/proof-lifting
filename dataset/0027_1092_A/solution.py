n = int(input())
a = ''
for i in range(97, 123):
    a += chr(i)
for i in range(n):
    n1, k = map(int, input().split())
    r = ''
    s = a[:k]
    while len(r) < n1:
        r += s
    r = r[:n1]
    print(r)