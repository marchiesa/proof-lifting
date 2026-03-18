import sys
input = sys.stdin.readline

t=int(input())

for testcases in range(t):
    a,b,c,d,k=map(int,input().split())

    x=-(a//(-c))
    y=-(b//(-d))

    if x+y<=k:
        print(x,y)
    else:
        print(-1)