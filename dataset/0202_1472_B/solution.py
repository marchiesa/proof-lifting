import sys
input = sys.stdin.readline
for _ in range(int(input())):
    n = int(input())
    A = list(map(int, input().split()))
    s = sum(A)
    if s % 2:
        print("NO")
    else:
        if A.count(2) % 2 and not A.count(1):
            print("NO")
        else:
            print("YES")