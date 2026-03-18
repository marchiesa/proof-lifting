import sys

input = sys.stdin.buffer.readline

for _ in range(int(input())):
    n,d = map(int,input().split())
    a = list(map(int,input().split()))
    a.sort()
    if a[1] > d:
        print("NO")
    else:
        for i in range(2,n):
            if min(a[0]+a[1],a[i]) > d:
                print("NO")
                break
        else:
            print("YES")