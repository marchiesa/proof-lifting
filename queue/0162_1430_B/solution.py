import sys
input = sys.stdin.buffer.readline

T = int(input())
for testcase in range(T):
    n,k = map(int,input().split())
    a = list(map(int,input().split()))
    a.sort()
    for i in range(k):
        if n-2-i == -1:
            break
        a[-1] += a[n-2-i]
        a[n-2-i] = 0
    
    print(max(a)-min(a))